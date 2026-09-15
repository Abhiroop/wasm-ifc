{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

{- | Elaboration: type-checking a decoded module and, where it succeeds, building the
  corresponding intrinsically-typed AST with its indices recovered — the bridge from the
  untyped (decoded) representation to the typed interpreter.

  Elaboration runs against a runtime witness of the module signature ('SModuleShape'), so it
  covers the whole module: @call@ between functions, globals and memory are all checked.
  Dead code after an unconditional transfer is validated under the spec's polymorphic
  stack ('validateDead'); nested block/loop/if bodies are fresh, reachable frames.
-}
module Validation.Elaborate (
    ElabError (..),
    OperandKind (..),
    IndexSpace (..),
    elaborateModule,
) where

import Control.Monad (foldM, when)
import Data.Text (Text)
import Data.Type.Equality ((:~:) (Refl))
import Data.Word (Word32)

import Data.List.Singletons ((%++))
import Data.Singletons (SomeSing (..), toSing)
import Data.Singletons.Base.TH (SList (SCons, SNil), Sing, fromSing)
import Data.Singletons.Decide (decideEquality)
import Runtime.MemInst (maxMemoryPages)
import Syntax.Functions (Function (..), FunctionSpace (..), RawFunction (RawFunction))
import Syntax.Globals (Global (..), GlobalSpace (..), RawGlobal (RawGlobal))
import Syntax.Immediates
import Syntax.Indices (DataIdx (..), FunctionIdx (..), GlobalIdx (..), LabelIdx (..), LocalIdx (..), MemoryIdx (..), TableIdx (..), TypeIdx (..))
import Syntax.Instructions (
    BitwiseOp (..),
    ConvertOp (..),
    CountOp (..),
    Expr (..),
    FloatBinOp (..),
    FloatUnOp (..),
    Instr (..),
    RawInstr (..),
    convertEnds,
 )
import Syntax.Module
import Syntax.Types
import Validation.Ref (resolveLocal)
import Validation.Reflect
import Validation.Shape

{- | Why a module is rejected. Each case carries what it is about — the instruction (by its
  spec name), the types or indices involved — rather than a formatted message, so callers and
  tests can match on the facts. Stacks are listed top first, as everywhere in the shapes.
-}
data ElabError
    = -- | the instruction needs more operands than the stack holds
      StackUnderflow Text
    | -- | an operand of the instruction has the wrong type: expected, actual
      OperandMismatch Text ValType ValType
    | -- | the stack does not hold the values the instruction or block expects: expected, actual
      StackMismatch Text [ValType] [ValType]
    | -- | the instruction's operand type is not of the kind it requires
      WrongOperandKind OperandKind ValType
    | -- | a memory instruction, or an active data segment, in a module without a memory
      NoMemory Text
    | -- | a memory access whose alignment exponent exceeds its width in bytes
      Misaligned Word32 Int
    | -- | not a narrow access width for the type
      InvalidNarrowWidth ValType Int
    | -- | @global.set@ on an immutable global
      ImmutableGlobal Word32
    | -- | an index into the named space is out of range
      IndexOutOfRange IndexSpace Word32
    | -- | a body left one stack where its type demands another: expected, actual
      ResultMismatch [ValType] [ValType]
    | -- | unreachable code with inconsistent known types: expected, found
      DeadCodeMismatch ValType ValType
    | -- | unreachable code left values above the polymorphic bottom at the end of its block
      DeadCodeLeftovers
    | -- | @br_table@ targets that do not agree with the default
      BrTableTargetsDiffer
    | -- | a typed @select@ whose annotation does not hold exactly one type
      InvalidSelectArity Int
    | -- | a global whose initializer is not a single constant of its type
      InvalidGlobalInitializer Word32
    | -- | sections whose lengths disagree
      Malformed Text
    | -- | an active data segment's offset is not a single @i32.const@
      InvalidDataSegmentOffset Int
    | -- | an element segment's offset is not a single @i32.const@
      InvalidElementSegmentOffset Int
    | -- | @call_indirect@, or an element segment, in a module without a table
      NoTable Text
    | -- | a table's limits are not well-formed
      InvalidTableLimits Limits
    | -- | a memory's limits are not well-formed or exceed 65536 pages
      InvalidMemoryLimits Limits
    | -- | more than one memory (the spec allows at most one)
      TooManyMemories
    | -- | two exports share this name
      DuplicateExport Text
    | -- | the start function is not of type @[] -> []@
      InvalidStartFunction
    deriving stock (Eq, Show)

-- | The sub-category an instruction requires its operand type to belong to.
data OperandKind = Numeric | Integral | FloatingPoint
    deriving stock (Eq, Show)

-- | The index spaces an instruction or export may refer into.
data IndexSpace = Locals | Globals | Functions | Labels | Memories | Types | Tables | DataSegments
    deriving stock (Eq, Show)

-- *** Elaboration environment & results ***

{- | What elaboration knows: the module signature witness, the enclosing function's result
  type and locals, and the result type of each enclosing label.
-}
data ElabEnv (shape :: ModuleShape) (ret :: ResultType) (locals :: [ValType]) (labels :: [ResultType]) = ElabEnv
    { shape :: Sing shape
    , types :: [FuncType]
    -- ^ the module's type section, which @call_indirect@ refers into
    , results :: Sing ret
    , locals :: Sing locals
    , labels :: Sing labels
    }

{- | The result of elaborating a whole instruction sequence that started from stack @stackIn@.
  A sequence either runs to its end or leaves early through an unconditional branch, and the
  two cases carry different evidence:
-}
data ElaboratedExpr (shape :: ModuleShape) (ret :: ResultType) (locals :: [ValType]) (labels :: [ResultType]) (stackIn :: [ValType]) where
    -- | Control reached the end of the sequence, leaving a concrete @stackOut@ on top.
    Reachable :: Sing stackOut -> Expr shape ('FrameShape locals ret) labels stackIn stackOut -> ElaboratedExpr shape ret locals labels stackIn
    {- | The sequence ended in an unconditional transfer (@br@ / @return@ / @unreachable@), so
    control never falls out the bottom. Nothing constrains the output stack, so it is left
    universally quantified — exactly the spec's stack-polymorphism for dead code. The
    'PolyStack' is what the dead tail leaves, still to be checked against the expected result.
    -}
    Diverged :: PolyStack -> (forall stackOut. Expr shape ('FrameShape locals ret) labels stackIn stackOut) -> ElaboratedExpr shape ret locals labels stackIn

{- | The result of elaborating a single instruction — the per-instruction version of
  'ElaboratedExpr', with the same two cases. 'elabSeq' folds these into an 'ElaboratedExpr'
  as it walks the sequence.
-}
data ElaboratedInstr (shape :: ModuleShape) (ret :: ResultType) (locals :: [ValType]) (labels :: [ResultType]) (stackIn :: [ValType]) where
    {- | An ordinary instruction: it leaves a concrete @stackOut@ and elaboration continues
    from there (the analogue of 'Reachable').
    -}
    Produces :: Sing stackOut -> Instr shape ('FrameShape locals ret) labels stackIn stackOut -> ElaboratedInstr shape ret locals labels stackIn
    {- | An unconditional transfer (@br@ / @return@ / @unreachable@): control leaves here, so any
    instructions after it are dead code and the output stack is unconstrained (the analogue
    of 'Diverged').
    -}
    Transfers :: (forall stackOut. Instr shape ('FrameShape locals ret) labels stackIn stackOut) -> ElaboratedInstr shape ret locals labels stackIn

note :: ElabError -> Maybe a -> Either ElabError a
note e = maybe (Left e) Right

-- *** Sequences ***

elabSeq ::
    ElabEnv shape ret locals labels ->
    Sing stackIn ->
    [RawInstr] ->
    Either ElabError (ElaboratedExpr shape ret locals labels stackIn)
elabSeq _ stackIn [] = Right (Reachable stackIn INil)
elabSeq env stackIn (raw : rest) = do
    elaboratedInstr <- elabInstr env stackIn raw
    case elaboratedInstr of
        Produces stackOut instr -> do
            rest' <- elabSeq env stackOut rest
            pure $ case rest' of
                Reachable stackOut' seq' -> Reachable stackOut' (instr :. seq')
                Diverged final poly -> Diverged final (instr :. poly)
        Transfers transfer -> do
            final <- validateDead env rest
            pure (Diverged final (transfer :. INil))

-- *** Single instructions ***

elabInstr ::
    forall shape ret locals labels stackIn.
    ElabEnv shape ret locals labels ->
    Sing stackIn ->
    RawInstr ->
    Either ElabError (ElaboratedInstr shape ret locals labels stackIn)
elabInstr env stackIn instr = case instr of
    {- Constants -}
    Const st literal -> do
        isNum <- requireNum st
        Right (Produces (SCons st stackIn) (IConst isNum literal))
    {- Numeric (consume two of type t, produce one of type t) -}
    Add st -> do
        isNum <- requireNum st
        consumeTwo st st stackIn (IAdd isNum)
    Sub st -> do
        isNum <- requireNum st
        consumeTwo st st stackIn (ISub isNum)
    Mul st -> do
        isNum <- requireNum st
        consumeTwo st st stackIn (IMul isNum)
    Div st sign -> do
        sn <- requireNumWithSign st sign
        consumeTwo st st stackIn (IDiv sn)
    Rem st sign -> do
        isInt <- requireInt st
        consumeTwo st st stackIn (IRem isInt sign)
    {- Comparison (consume two of type t, produce one i32). @eqz@ is integer-only. -}
    Eq st -> do
        isNum <- requireNum st
        consumeTwo st SI32 stackIn (IEq isNum)
    Ne st -> do
        isNum <- requireNum st
        consumeTwo st SI32 stackIn (INe isNum)
    Lt st sign -> do
        sn <- requireNumWithSign st sign
        consumeTwo st SI32 stackIn (ILt sn)
    Gt st sign -> do
        sn <- requireNumWithSign st sign
        consumeTwo st SI32 stackIn (IGt sn)
    Le st sign -> do
        sn <- requireNumWithSign st sign
        consumeTwo st SI32 stackIn (ILe sn)
    Ge st sign -> do
        sn <- requireNumWithSign st sign
        consumeTwo st SI32 stackIn (IGe sn)
    Eqz st -> case stackIn of
        SCons sa rest -> do
            isInt <- requireInt st
            Refl <- note (OperandMismatch "eqz" (valTypeOf st) (valTypeOf sa)) (decideEquality sa st)
            Right (Produces (SCons SI32 rest) (IEqz isInt))
        _ -> Left (StackUnderflow "eqz")
    {- Stack management -}
    Drop -> case stackIn of
        SCons _ rest -> Right (Produces rest IDrop)
        _ -> Left (StackUnderflow "drop")
    Select -> elabSelect Nothing stackIn
    SelectTyped [t] -> elabSelect (Just t) stackIn
    SelectTyped ts -> Left (InvalidSelectArity (length ts))
    {- Locals -}
    LocalGet (LocalIdx i) -> case mkLocalElem (env.locals) i of
        Just (SomeElem sv ix) -> Right (Produces (SCons sv stackIn) (ILocalGet (resolveLocal sv ix)))
        Nothing -> Left (IndexOutOfRange Locals i)
    LocalSet (LocalIdx i) -> case mkLocalElem (env.locals) i of
        Just (SomeElem sv ix) -> case stackIn of
            SCons stop rest -> do
                Refl <- note (OperandMismatch "local.set" (valTypeOf sv) (valTypeOf stop)) (decideEquality stop sv)
                Right (Produces rest (ILocalSet (resolveLocal sv ix)))
            _ -> Left (StackUnderflow "local.set")
        Nothing -> Left (IndexOutOfRange Locals i)
    LocalTee (LocalIdx i) -> case mkLocalElem (env.locals) i of
        Just (SomeElem sv ix) -> case stackIn of
            SCons stop _ -> do
                Refl <- note (OperandMismatch "local.tee" (valTypeOf sv) (valTypeOf stop)) (decideEquality stop sv)
                Right (Produces stackIn (ILocalTee (resolveLocal sv ix)))
            _ -> Left (StackUnderflow "local.tee")
        Nothing -> Left (IndexOutOfRange Locals i)
    {- Globals -}
    GlobalGet (GlobalIdx g) -> case lookupGlobalRef (globalTypesSing (env.shape)) g of
        Nothing -> Left (IndexOutOfRange Globals g)
        Just (SomeGlobalRef _ st gix) -> Right (Produces (SCons st stackIn) (IGlobalGet gix))
    GlobalSet (GlobalIdx g) -> case lookupGlobalRef (globalTypesSing (env.shape)) g of
        Nothing -> Left (IndexOutOfRange Globals g)
        Just (SomeGlobalRef smut st gix) -> case smut of
            SImmutable -> Left (ImmutableGlobal g)
            SMutable -> case stackIn of
                SCons stop rest -> do
                    Refl <- note (OperandMismatch "global.set" (valTypeOf st) (valTypeOf stop)) (decideEquality stop st)
                    Right (Produces rest (IGlobalSet gix))
                _ -> Left (StackUnderflow "global.set")
    {- Memory -}
    Load st memArg -> case stackIn of
        SCons sc rest -> do
            NonEmptyMems <- requireMemory env "load"
            isNum <- requireNum st
            Refl <- note (OperandMismatch "load" I32 (valTypeOf sc)) (decideEquality sc SI32)
            checkAlign memArg (numBytes isNum)
            Right (Produces (SCons st rest) (ILoad isNum memArg))
        _ -> Left (StackUnderflow "load")
    Store st memArg -> case stackIn of
        SCons sv (SCons sc rest) -> do
            NonEmptyMems <- requireMemory env "store"
            isNum <- requireNum st
            Refl <- note (OperandMismatch "store" (valTypeOf st) (valTypeOf sv)) (decideEquality sv st)
            Refl <- note (OperandMismatch "store" I32 (valTypeOf sc)) (decideEquality sc SI32)
            checkAlign memArg (numBytes isNum)
            Right (Produces rest (IStore isNum memArg))
        _ -> Left (StackUnderflow "store")
    LoadN st width sign memArg -> case stackIn of
        SCons sc rest -> do
            NonEmptyMems <- requireMemory env "load"
            nw <- requireNarrow st width
            Refl <- note (OperandMismatch "load" I32 (valTypeOf sc)) (decideEquality sc SI32)
            checkAlign memArg (narrowBytes nw)
            Right (Produces (SCons st rest) (ILoadN nw sign memArg))
        _ -> Left (StackUnderflow "load")
    StoreN st width memArg -> case stackIn of
        SCons sv (SCons sc rest) -> do
            NonEmptyMems <- requireMemory env "store"
            nw <- requireNarrow st width
            Refl <- note (OperandMismatch "store" (valTypeOf st) (valTypeOf sv)) (decideEquality sv st)
            Refl <- note (OperandMismatch "store" I32 (valTypeOf sc)) (decideEquality sc SI32)
            checkAlign memArg (narrowBytes nw)
            Right (Produces rest (IStoreN nw memArg))
        _ -> Left (StackUnderflow "store")
    MemorySize -> do
        NonEmptyMems <- requireMemory env "memory.size"
        Right (Produces (SCons SI32 stackIn) IMemSize)
    MemoryCopy -> do
        NonEmptyMems <- requireMemory env "memory.copy"
        threeAddresses "memory.copy" stackIn IMemCopy
    MemoryFill -> do
        NonEmptyMems <- requireMemory env "memory.fill"
        threeAddresses "memory.fill" stackIn IMemFill
    MemoryInit (DataIdx d) -> do
        NonEmptyMems <- requireMemory env "memory.init"
        segmentIx <- note (IndexOutOfRange DataSegments d) (mkDataElem (dataShapesSing (env.shape)) d)
        threeAddresses "memory.init" stackIn (IMemInit segmentIx)
    DataDrop (DataIdx d) -> do
        segmentIx <- note (IndexOutOfRange DataSegments d) (mkDataElem (dataShapesSing (env.shape)) d)
        Right (Produces stackIn (IDataDrop segmentIx))
    MemoryGrow -> case stackIn of
        SCons sc rest -> do
            NonEmptyMems <- requireMemory env "memory.grow"
            Refl <- note (OperandMismatch "memory.grow" I32 (valTypeOf sc)) (decideEquality sc SI32)
            Right (Produces (SCons SI32 rest) IMemGrow)
        _ -> Left (StackUnderflow "memory.grow")
    {- Calls -}
    CallIndirect (TypeIdx t) -> case stackIn of
        SCons sc rest -> do
            NonEmptyTables <- requireTable env
            Refl <- note (OperandMismatch "call_indirect" I32 (valTypeOf sc)) (decideEquality sc SI32)
            expected <- note (IndexOutOfRange Types t) (nth (env.types) t)
            case toSing (stackOrderFuncType expected) of
                SomeSing (SFuncType psS rsS) -> case matchPrefix psS rest of
                    Nothing -> Left (StackMismatch "call_indirect" (stackToList psS) (stackToList rest))
                    Just (SomeSplit sS witness) -> Right (Produces (rsS %++ sS) (ICallIndirect witness (SFuncType psS rsS)))
        _ -> Left (StackUnderflow "call_indirect")
    Call (FunctionIdx f) -> case lookupFuncRef (funcTypesSing (env.shape)) f of
        Nothing -> Left (IndexOutOfRange Functions f)
        Just (SomeFuncRef psS rsS fix) -> case matchPrefix psS stackIn of
            Nothing -> Left (StackMismatch "call" (stackToList psS) (stackToList stackIn))
            Just (SomeSplit sS witness) -> Right (Produces (rsS %++ sS) (ICall witness fix))
    {- Integer bitwise / shift / count (integer types only) -}
    And st -> do
        isInt <- requireInt st
        sameTypeBinary st stackIn (IBitwise isInt BwAnd)
    Or st -> do
        isInt <- requireInt st
        sameTypeBinary st stackIn (IBitwise isInt BwOr)
    Xor st -> do
        isInt <- requireInt st
        sameTypeBinary st stackIn (IBitwise isInt BwXor)
    Shl st -> do
        isInt <- requireInt st
        sameTypeBinary st stackIn (IBitwise isInt BwShl)
    Shr st sign -> do
        isInt <- requireInt st
        sameTypeBinary st stackIn (IBitwise isInt (BwShr sign))
    Rotl st -> do
        isInt <- requireInt st
        sameTypeBinary st stackIn (IBitwise isInt BwRotl)
    Rotr st -> do
        isInt <- requireInt st
        sameTypeBinary st stackIn (IBitwise isInt BwRotr)
    Clz st -> do
        isInt <- requireInt st
        sameTypeUnary st stackIn (ICount isInt OpClz)
    Ctz st -> do
        isInt <- requireInt st
        sameTypeUnary st stackIn (ICount isInt OpCtz)
    Popcnt st -> do
        isInt <- requireInt st
        sameTypeUnary st stackIn (ICount isInt OpPopcnt)
    {- Floating-point unary / binary (floating-point types only) -}
    Abs st -> do
        isFloat <- requireFloat st
        sameTypeUnary st stackIn (IFloatUn isFloat FAbs)
    Neg st -> do
        isFloat <- requireFloat st
        sameTypeUnary st stackIn (IFloatUn isFloat FNeg)
    Sqrt st -> do
        isFloat <- requireFloat st
        sameTypeUnary st stackIn (IFloatUn isFloat FSqrt)
    Ceil st -> do
        isFloat <- requireFloat st
        sameTypeUnary st stackIn (IFloatUn isFloat FCeil)
    Floor st -> do
        isFloat <- requireFloat st
        sameTypeUnary st stackIn (IFloatUn isFloat FFloor)
    FloatTrunc st -> do
        isFloat <- requireFloat st
        sameTypeUnary st stackIn (IFloatUn isFloat FTrunc)
    Nearest st -> do
        isFloat <- requireFloat st
        sameTypeUnary st stackIn (IFloatUn isFloat FNearest)
    Min st -> do
        isFloat <- requireFloat st
        sameTypeBinary st stackIn (IFloatBin isFloat FMin)
    Max st -> do
        isFloat <- requireFloat st
        sameTypeBinary st stackIn (IFloatBin isFloat FMax)
    Copysign st -> do
        isFloat <- requireFloat st
        sameTypeBinary st stackIn (IFloatBin isFloat FCopysign)
    {- Conversions: the opcode's own type indices are the source/result -}
    Convert op ->
        let (nf, nt) = convertEnds op
         in case stackIn of
                SCons sa rest -> do
                    Refl <- note (OperandMismatch "conversion" (fromSing (numSing nf)) (valTypeOf sa)) (decideEquality sa (numSing nf))
                    Right (Produces (SCons (numSing nt) rest) (IConvert op))
                _ -> Left (StackUnderflow "conversion")
    {- Inert -}
    Nop -> Right (Produces stackIn INop)
    {- Structured control -}
    Block (FuncType psT rsT) body ->
        case (reflectStack (stackOrder psT), reflectStack (stackOrder rsT)) of
            (SomeStack psS, SomeStack rsS) -> case matchPrefix psS stackIn of
                Nothing -> Left (StackMismatch "block" (stackToList psS) (stackToList stackIn))
                Just (SomeSplit sS witness) ->
                    elabBodyChecked (pushLabel rsS env) psS rsS body $ \bodySeq ->
                        Right (Produces (rsS %++ sS) (IBlock witness bodySeq))
    Loop (FuncType psT rsT) body ->
        case (reflectStack (stackOrder psT), reflectStack (stackOrder rsT)) of
            (SomeStack psS, SomeStack rsS) -> case matchPrefix psS stackIn of
                Nothing -> Left (StackMismatch "loop" (stackToList psS) (stackToList stackIn))
                Just (SomeSplit sS witness) ->
                    elabBodyChecked (pushLabel psS env) psS rsS body $ \bodySeq ->
                        Right (Produces (rsS %++ sS) (ILoop witness bodySeq))
    If (FuncType psT rsT) thenBody elseBody -> case stackIn of
        SCons sc rest -> do
            Refl <- note (OperandMismatch "if" I32 (valTypeOf sc)) (decideEquality sc SI32)
            case (reflectStack (stackOrder psT), reflectStack (stackOrder rsT)) of
                (SomeStack psS, SomeStack rsS) -> case matchPrefix psS rest of
                    Nothing -> Left (StackMismatch "if" (stackToList psS) (stackToList rest))
                    Just (SomeSplit sS witness) ->
                        elabBodyChecked (pushLabel rsS env) psS rsS thenBody $ \thenSeq ->
                            elabBodyChecked (pushLabel rsS env) psS rsS elseBody $ \elseSeq ->
                                Right (Produces (rsS %++ sS) (IIf witness thenSeq elseSeq))
        _ -> Left (StackUnderflow "if")
    {- Branches (unconditional ones diverge) -}
    Br (LabelIdx l) -> case mkLabelElem (env.labels) l of
        Nothing -> Left (IndexOutOfRange Labels l)
        Just (SomeLabel rsS labelIx) -> case matchPrefix rsS stackIn of
            Nothing -> Left (StackMismatch "br" (stackToList rsS) (stackToList stackIn))
            Just (SomeSplit _ witness) -> Right (Transfers (IBr witness labelIx))
    BrIf (LabelIdx l) -> case stackIn of
        SCons sc rest -> do
            Refl <- note (OperandMismatch "br_if" I32 (valTypeOf sc)) (decideEquality sc SI32)
            case mkLabelElem (env.labels) l of
                Nothing -> Left (IndexOutOfRange Labels l)
                Just (SomeLabel rsS labelIx) -> case matchPrefix rsS rest of
                    Nothing -> Left (StackMismatch "br_if" (stackToList rsS) (stackToList rest))
                    Just (SomeSplit _ witness) -> Right (Produces rest (IBrIf witness labelIx))
        _ -> Left (StackUnderflow "br_if")
    BrTable targets (LabelIdx d) -> case stackIn of
        SCons sc rest -> case decideEquality sc SI32 of
            Nothing -> Left (OperandMismatch "br_table" I32 (valTypeOf sc))
            Just Refl -> case mkLabelElem (env.labels) d of
                Nothing -> Left (IndexOutOfRange Labels d)
                Just (SomeLabel rsS defIx) -> case mapM (resolveTarget env rsS) targets of
                    Left err -> Left err
                    Right targetIxs -> case matchPrefix rsS rest of
                        Nothing -> Left (StackMismatch "br_table" (stackToList rsS) (stackToList rest))
                        Just (SomeSplit _ witness) -> Right (Transfers (IBrTable witness targetIxs defIx))
        _ -> Left (StackUnderflow "br_table")
    Return -> case matchPrefix (env.results) stackIn of
        Nothing -> Left (StackMismatch "return" (stackToList (env.results)) (stackToList stackIn))
        Just (SomeSplit _ witness) -> Right (Transfers (IReturn witness))
    Unreachable -> Right (Transfers IUnreachable)

-- | Push a label's result type onto the elaboration environment's label context.

{- | @select@ takes a condition over two operands of one numeric type; the typed form also
  names that type, which the operands must have.
-}
elabSelect :: Maybe ValType -> Sing stackIn -> Either ElabError (ElaboratedInstr shape ret locals labels stackIn)
elabSelect annotation stackIn = case stackIn of
    SCons sc (SCons va (SCons vb rest)) -> do
        Refl <- note (OperandMismatch "select" I32 (valTypeOf sc)) (decideEquality sc SI32)
        Refl <- note (OperandMismatch "select" (valTypeOf va) (valTypeOf vb)) (decideEquality va vb)
        mapM_ (\t -> if t == valTypeOf va then Right () else Left (OperandMismatch "select" t (valTypeOf va))) annotation
        isNum <- requireNum va
        Right (Produces (SCons va rest) (ISelect isNum))
    _ -> Left (StackUnderflow "select")

pushLabel :: Sing rs -> ElabEnv shape ret locals labels -> ElabEnv shape ret locals (rs ': labels)
pushLabel rsS env = env {labels = SCons rsS (env.labels)}

{- | Elaborate a block/loop/if body (its label already pushed onto @env@), checking it
  transforms @ps@ into @rs@, and hand the resulting typed sequence to the continuation.
-}
elabBodyChecked ::
    ElabEnv shape ret locals labels ->
    Sing ps ->
    Sing rs ->
    [RawInstr] ->
    (Expr shape ('FrameShape locals ret) labels ps rs -> Either ElabError a) ->
    Either ElabError a
elabBodyChecked env psS rsS body k = do
    body' <- elabSeq env psS body
    case body' of
        Reachable soS seq' -> do
            Refl <- note (ResultMismatch (stackToList rsS) (stackToList soS)) (decideEquality soS rsS)
            k seq'
        Diverged final poly -> do
            checkDeadResult final rsS
            k poly

-- | Resolve one @br_table@ target, checking it carries the same result type as the rest.
resolveTarget :: ElabEnv shape ret locals labels -> Sing rs -> LabelIdx -> Either ElabError (Elem rs labels)
resolveTarget env rsS (LabelIdx t) = case mkLabelElem (env.labels) t of
    Nothing -> Left (IndexOutOfRange Labels t)
    Just (SomeLabel rsS' targetIx) -> case decideEquality rsS' rsS of
        Just Refl -> Right targetIx
        Nothing -> Left BrTableTargetsDiffer

{- | Require an operation's operand type to be numeric (resp. integer, floating-point),
  yielding the evidence, or fail elaboration (e.g. @funcref.add@, @f32.and@, @i32.sqrt@).
  The evidence is what lets the typed instruction carry the exact constraint the spec
  demands, and lets the interpreter dispatch on it totally.
-}
requireNum :: Sing (t :: ValType) -> Either ElabError (IsNum t)
requireNum st = note (WrongOperandKind Numeric (valTypeOf st)) (decideNum st)

requireInt :: Sing (t :: ValType) -> Either ElabError (IsInt t)
requireInt st = note (WrongOperandKind Integral (valTypeOf st)) (decideInt st)

requireFloat :: Sing (t :: ValType) -> Either ElabError (IsFloat t)
requireFloat st = note (WrongOperandKind FloatingPoint (valTypeOf st)) (decideFloat st)

{- | Require a numeric operand for @div@ and the ordered comparisons, keeping the signedness
  for integers and dropping it for floats (so a signed float comparison is unrepresentable).
-}
requireNumWithSign :: Sing (t :: ValType) -> Signedness -> Either ElabError (NumWithSign t)
requireNumWithSign st sign =
    note (WrongOperandKind Numeric (valTypeOf st)) (decideNumWithSign st sign)

{- | Require a valid narrow access width for an integer type (so @i32.load8@ is fine, a
  four-byte narrow access of an i32 is not).
-}
requireNarrow :: Sing (t :: ValType) -> Int -> Either ElabError (NarrowWidth t)
requireNarrow st width =
    note (InvalidNarrowWidth (valTypeOf st) width) (decideNarrow st width)

{- | The bulk-memory instructions consume three i32 operands; the typed instruction is
  polymorphic in what lies beneath.
-}
threeAddresses ::
    Text ->
    Sing stackIn ->
    (forall s. Instr shape ('FrameShape locals ret) labels ('I32 ': 'I32 ': 'I32 ': s) s) ->
    Either ElabError (ElaboratedInstr shape ret locals labels stackIn)
threeAddresses name stackIn typed = case stackIn of
    SCons a (SCons b (SCons c rest)) -> do
        Refl <- note (OperandMismatch name I32 (valTypeOf a)) (decideEquality a SI32)
        Refl <- note (OperandMismatch name I32 (valTypeOf b)) (decideEquality b SI32)
        Refl <- note (OperandMismatch name I32 (valTypeOf c)) (decideEquality c SI32)
        Right (Produces rest typed)
    _ -> Left (StackUnderflow name)

-- | Require the module to declare a table, for @call_indirect@.
requireTable :: ElabEnv shape ret locals labels -> Either ElabError (NonEmptyTables (ModuleTables shape))
requireTable env = note (NoTable "call_indirect") (tablesNonEmpty (tableShapesSing (env.shape)))

-- | Total list indexing by a decoded index.
nth :: [a] -> Word32 -> Maybe a
nth xs i = case drop (fromIntegral i) xs of
    x : _ -> Just x
    [] -> Nothing

{- | Require the module to declare a memory. The proof licenses the
  @ModuleMems shape ~ (mem ': mems)@ constraint the typed memory instructions carry.
-}
requireMemory ::
    ElabEnv shape ret locals labels ->
    Text ->
    Either ElabError (NonEmptyMems (ModuleMems shape))
requireMemory env instrName =
    note (NoMemory instrName) (memsNonEmpty (memShapesSing (env.shape)))

{- | The spec bounds a memory access's alignment by its width: @2^align <= accessBytes@. The
  binary format stores @align@ as the log2 exponent, so a valid exponent is at most 3 (for an
  8-byte access); anything larger is rejected without computing an overflowing @2^align@.
-}
checkAlign :: MemArg -> Int -> Either ElabError ()
checkAlign memArg accessBytes
    | align <= 3 && (2 ^ align :: Int) <= accessBytes = Right ()
    | otherwise = Left (Misaligned memArg.alignment accessBytes)
  where
    align = fromIntegral memArg.alignment :: Int

consumeTwo ::
    forall t r shape ret locals labels stackIn.
    Sing (t :: ValType) ->
    Sing (r :: ValType) ->
    Sing stackIn ->
    (forall s. Instr shape ('FrameShape locals ret) labels (t ': t ': s) (r ': s)) ->
    Either ElabError (ElaboratedInstr shape ret locals labels stackIn)
consumeTwo st sr stackIn typed = case stackIn of
    SCons sa (SCons sb rest) -> do
        Refl <- note (OperandMismatch "binary operation" (valTypeOf st) (valTypeOf sa)) (decideEquality sa st)
        Refl <- note (OperandMismatch "binary operation" (valTypeOf st) (valTypeOf sb)) (decideEquality sb st)
        Right (Produces (SCons sr rest) typed)
    _ -> Left (StackUnderflow "binary operation")

-- | A binary operation whose result has the same type as its (matching) operands.
sameTypeBinary ::
    Sing (t :: ValType) ->
    Sing stackIn ->
    (forall s. Instr shape ('FrameShape locals ret) labels (t ': t ': s) (t ': s)) ->
    Either ElabError (ElaboratedInstr shape ret locals labels stackIn)
sameTypeBinary st = consumeTwo st st

-- | A unary operation whose result has the same type as its operand.
sameTypeUnary ::
    Sing (t :: ValType) ->
    Sing stackIn ->
    (forall s. Instr shape ('FrameShape locals ret) labels (t ': s) (t ': s)) ->
    Either ElabError (ElaboratedInstr shape ret locals labels stackIn)
sameTypeUnary st stackIn typed = case stackIn of
    SCons sa rest -> do
        Refl <- note (OperandMismatch "unary operation" (valTypeOf st) (valTypeOf sa)) (decideEquality sa st)
        Right (Produces (SCons st rest) typed)
    _ -> Left (StackUnderflow "unary operation")

{- *** Unreachable code (full unreachable typing) ***

   After an unconditional transfer the operand stack becomes polymorphic. We validate the
   dead tail over a 'PolyStack' — known entries above an implicit @Unknown@ bottom — so
   underflowing pops yield @Unknown@ (and succeed), exactly as the spec prescribes. Nested
   block/loop/if bodies are fresh reachable frames, validated by the ordinary elaborator.
-}

newtype PolyStack = PolyStack [Maybe ValType]

pushKnown :: ValType -> PolyStack -> PolyStack
pushKnown v (PolyStack xs) = PolyStack (Just v : xs)

popAny :: PolyStack -> (Maybe ValType, PolyStack)
popAny (PolyStack (x : xs)) = (x, PolyStack xs)
popAny (PolyStack []) = (Nothing, PolyStack [])

popKnown :: ValType -> PolyStack -> Either ElabError PolyStack
popKnown t s = case popAny s of
    (Nothing, s') -> Right s'
    (Just v, s')
        | v == t -> Right s'
        | otherwise -> Left (DeadCodeMismatch t v)

validateDead :: ElabEnv shape ret locals labels -> [RawInstr] -> Either ElabError PolyStack
validateDead env = go (PolyStack [])
  where
    go s [] = Right s
    go s (i : is) = stepDead env s i >>= \s' -> go s' is

{- | A dead tail must still end with the block's result type: each expected type is popped
  (a known entry must match, an unknown one may be anything) and nothing may be left above the
  polymorphic bottom.
-}
checkDeadResult :: PolyStack -> Sing (rs :: [ValType]) -> Either ElabError ()
checkDeadResult final rsS = do
    remaining <- foldM (flip popKnown) final (stackToList rsS)
    case unStack remaining of
        [] -> Right ()
        _ -> Left DeadCodeLeftovers

stepDead :: ElabEnv shape ret locals labels -> PolyStack -> RawInstr -> Either ElabError PolyStack
stepDead env s instr = case instr of
    Const t _ -> Right (pushKnown (valTypeOf t) s)
    Add t -> arith t
    Sub t -> arith t
    Mul t -> arith t
    Div t _ -> arith t
    Rem t _ -> arith t
    Eq t -> compare' t
    Ne t -> compare' t
    Lt t _ -> compare' t
    Gt t _ -> compare' t
    Le t _ -> compare' t
    Ge t _ -> compare' t
    Eqz t -> pushKnown I32 <$> popKnown (valTypeOf t) s
    Drop -> Right (snd (popAny s))
    Select -> do
        s1 <- popKnown I32 s
        let (a, s2) = popAny s1
            (b, s3) = popAny s2
        case (a, b) of
            (Just x, Just y) | x /= y -> Left (DeadCodeMismatch x y)
            _ -> Right (PolyStack (orElse a b : unStack s3))
    SelectTyped [t] -> popKnown I32 s >>= popKnown t >>= popKnown t >>= Right . pushKnown t
    SelectTyped ts -> Left (InvalidSelectArity (length ts))
    LocalGet (LocalIdx i) -> withLocal env i (\v -> Right (pushKnown v s))
    LocalSet (LocalIdx i) -> withLocal env i (\v -> popKnown v s)
    LocalTee (LocalIdx i) -> withLocal env i (\v -> pushKnown v <$> popKnown v s)
    GlobalGet (GlobalIdx g) -> case lookupGlobalRef (globalTypesSing (env.shape)) g of
        Nothing -> Left (IndexOutOfRange Globals g)
        Just (SomeGlobalRef _ st _) -> Right (pushKnown (valTypeOf st) s)
    GlobalSet (GlobalIdx g) -> case lookupGlobalRef (globalTypesSing (env.shape)) g of
        Nothing -> Left (IndexOutOfRange Globals g)
        Just (SomeGlobalRef _ st _) -> popKnown (valTypeOf st) s
    Load t _ -> pushKnown (valTypeOf t) <$> popKnown I32 s
    Store t _ -> popKnown (valTypeOf t) s >>= popKnown I32
    LoadN t _ _ _ -> pushKnown (valTypeOf t) <$> popKnown I32 s
    StoreN t _ _ -> popKnown (valTypeOf t) s >>= popKnown I32
    MemorySize -> Right (pushKnown I32 s)
    MemoryGrow -> pushKnown I32 <$> popKnown I32 s
    MemoryCopy -> popTypes [I32, I32, I32] s
    MemoryFill -> popTypes [I32, I32, I32] s
    MemoryInit _ -> popTypes [I32, I32, I32] s
    DataDrop _ -> Right s
    And t -> arith t
    Or t -> arith t
    Xor t -> arith t
    Shl t -> arith t
    Shr t _ -> arith t
    Rotl t -> arith t
    Rotr t -> arith t
    Clz t -> sameUnary t
    Ctz t -> sameUnary t
    Popcnt t -> sameUnary t
    Abs t -> sameUnary t
    Neg t -> sameUnary t
    Sqrt t -> sameUnary t
    Ceil t -> sameUnary t
    Floor t -> sameUnary t
    FloatTrunc t -> sameUnary t
    Nearest t -> sameUnary t
    Min t -> arith t
    Max t -> arith t
    Copysign t -> arith t
    Convert op -> let (from, to) = convertSig op in pushKnown to <$> popKnown from s
    Call (FunctionIdx f) -> case lookupFuncRef (funcTypesSing (env.shape)) f of
        Nothing -> Left (IndexOutOfRange Functions f)
        Just (SomeFuncRef psS rsS _) -> afterFrame (stackToList psS) (stackToList rsS) s
    CallIndirect (TypeIdx t) -> do
        s1 <- popKnown I32 s
        FuncType ps rs <- note (IndexOutOfRange Types t) (nth (env.types) t)
        afterFrame (stackOrder ps) (stackOrder rs) s1
    Nop -> Right s
    Block (FuncType psT rsT) body ->
        validateFrame env rsT psT rsT body >> afterFrame (stackOrder psT) (stackOrder rsT) s
    Loop (FuncType psT rsT) body ->
        validateFrame env psT psT rsT body >> afterFrame (stackOrder psT) (stackOrder rsT) s
    If (FuncType psT rsT) thenB elseB -> do
        s1 <- popKnown I32 s
        validateFrame env rsT psT rsT thenB
        validateFrame env rsT psT rsT elseB
        afterFrame (stackOrder psT) (stackOrder rsT) s1
    {- The transfers follow the spec's validation algorithm: pop what the target expects
       (checking the known entries), and after an unconditional one the stack is polymorphic
       again — an empty 'PolyStack' over the implicit unknown bottom. -}
    Br (LabelIdx l) -> do
        ts <- labelTypes env l
        _ <- popTypes ts s
        Right (PolyStack [])
    BrIf (LabelIdx l) -> do
        s1 <- popKnown I32 s
        ts <- labelTypes env l
        pushTypes ts <$> popTypes ts s1
    BrTable targets (LabelIdx d) -> do
        s1 <- popKnown I32 s
        defaultTypes <- labelTypes env d
        mapM_ (checkTarget s1 (length defaultTypes)) targets
        _ <- popTypes defaultTypes s1
        Right (PolyStack [])
    Return -> do
        _ <- popTypes (stackToList (env.results)) s
        Right (PolyStack [])
    Unreachable -> Right (PolyStack [])
  where
    -- A br_table target must have the default's arity and be poppable from the same stack.
    checkTarget s1 arity (LabelIdx t) = do
        ts <- labelTypes env t
        when (length ts /= arity) (Left BrTableTargetsDiffer)
        _ <- popTypes ts s1
        Right ()
    arith :: Sing (t :: ValType) -> Either ElabError PolyStack
    arith t = pushKnown (valTypeOf t) <$> (popKnown (valTypeOf t) s >>= popKnown (valTypeOf t))
    compare' :: Sing (t :: ValType) -> Either ElabError PolyStack
    compare' t = pushKnown I32 <$> (popKnown (valTypeOf t) s >>= popKnown (valTypeOf t))
    sameUnary :: Sing (t :: ValType) -> Either ElabError PolyStack
    sameUnary t = pushKnown (valTypeOf t) <$> popKnown (valTypeOf t) s

{- | The source and result value types of a conversion (for dead-code validation), read off
  the opcode's type indices via 'convertEnds'.
-}
convertSig :: ConvertOp from to -> (ValType, ValType)
convertSig op = let (nf, nt) = convertEnds op in (fromSing (numSing nf), fromSing (numSing nt))

{- | Validate a nested block/loop/if body — a fresh, reachable frame — discarding its AST. The
  label, parameter and result lists come straight from the decoded block type (declared order).
-}
validateFrame ::
    ElabEnv shape ret locals labels ->
    [ValType] ->
    [ValType] ->
    [ValType] ->
    [RawInstr] ->
    Either ElabError ()
validateFrame env labelT psT rsT body =
    case (reflectStack (stackOrder labelT), reflectStack (stackOrder psT), reflectStack (stackOrder rsT)) of
        (SomeStack labS, SomeStack psS, SomeStack rsS) ->
            elabBodyChecked (pushLabel labS env) psS rsS body (\_ -> Right ())

{- | The polymorphic stack after a frame (block/loop/if/call) in dead code: its parameters are
  popped and its results pushed. Both lists are in stack order (top first).
-}
afterFrame :: [ValType] -> [ValType] -> PolyStack -> Either ElabError PolyStack
afterFrame psT rsT s = Right (pushResults rsT (popN (length psT) s))
  where
    popN 0 t = t
    popN n t = popN (n - 1) (snd (popAny t))
    pushResults vs t = foldr pushKnown t vs

withLocal :: ElabEnv shape ret locals labels -> Word32 -> (ValType -> Either ElabError a) -> Either ElabError a
withLocal env i k = case mkLocalElem (env.locals) i of
    Just (SomeElem sv _) -> k (valTypeOf sv)
    Nothing -> Left (IndexOutOfRange Locals i)

-- | The result types of a label, in stack order.
labelTypes :: ElabEnv shape ret locals labels -> Word32 -> Either ElabError [ValType]
labelTypes env l = case mkLabelElem (env.labels) l of
    Just (SomeLabel rsS _) -> Right (stackToList rsS)
    Nothing -> Left (IndexOutOfRange Labels l)

-- | Pop a list of types given in stack order (top first); known entries must match.
popTypes :: [ValType] -> PolyStack -> Either ElabError PolyStack
popTypes ts s = foldM (flip popKnown) s ts

-- | Push a list of types given in stack order (top first).
pushTypes :: [ValType] -> PolyStack -> PolyStack
pushTypes ts s = foldr pushKnown s ts

{- | The term-level value type a value-type singleton stands for (and, lifted, a whole stack
  shape). Now that 'ValType' is flat, these are exactly the library's 'fromSing'.
-}
valTypeOf :: Sing (t :: ValType) -> ValType
valTypeOf = fromSing

stackToList :: Sing (s :: [ValType]) -> [ValType]
stackToList = fromSing

orElse :: Maybe a -> Maybe a -> Maybe a
orElse (Just x) _ = Just x
orElse Nothing y = y

unStack :: PolyStack -> [Maybe ValType]
unStack (PolyStack xs) = xs

-- *** Whole-module elaboration ***

{- | Type-check an entire decoded module: check its structure, build its shape, elaborate
  every function against it, evaluate the global initializers and segment offsets, resolve
  the element segments' and start function's indices. The result is a validated 'Module';
  "Runtime.Instantiate" turns it into a running instance.

  TODO(ifc P0): where do labels come from? A decoded 'RawModule' carries none and the binary
  format has no place for them. SecWasm's answer (§6, Usability): "the developer would have to
  manually annotate the function types and the load and store operations with security labels";
  everything else is derived. So the /policy/ is exactly: (1) per function type, the labels of
  parameters and results and the pc bound (@τ* →ℓ τ*@); (2) per global, its label; (3) per
  @load@/@store@ site, the immediate @ℓ@; and, our extension, (4) per host function, its
  labelled type (see "Runtime.Host"). Recommended carrier: a WebAssembly /custom section/
  (say @"ifc"@), which travels with the module, keeps it valid for every other tool (wabt and
  wasmtime preserve custom sections; the decoder already skips them, @custom.wast@ passes), and
  is keyed by function index, global index and code offset. Recommended defaults so unannotated
  modules still elaborate: a store's immediate is /inferred/ as @pc ⊔ ℓa ⊔ ℓv@, the least label
  that satisfies T-STORE and the most precise labelling of memory (no annotation ever needed for
  stores); a load's immediate defaults to 'Low ("I expect public bytes"), which is precise and
  traps at run time exactly where a secret is read unannotated (SecWasm's Example 1), so the
  trap tells you where an annotation belongs; function types and globals default to 'Low with
  pc bound 'Low, i.e. today's behaviour. Everything inside a function body is then determined:
  explicit flows are joins, the block pcs come from the pre-pass described at
  'Syntax.InstructionsIFC.IBlock' (a joint fixpoint of label propagation and pc assignment,
  cheap over two points; re-elaborating a block body at a higher pc is just calling the body
  elaborator again with another pc argument), and the elaborator inserts an @IRelabel@ wherever
  SecWasm's subtyping would apply (call arguments, block results, sets). Elaboration can only
  fail at a flow check, and 'ElabError' gains one constructor for it: which instruction, which
  flow (from which label into which). Intuition for staging: a second elaboration pass over the
  /typed/ 'Instr' (labels never change what is on the stack, only how it is typed), or folded
  into this pass once the P0 structure decision makes 'Instr' labelled.
-}
elaborateModule :: RawModule -> Either ElabError SomeModule
elaborateModule m = do
    validateStructure m
    case reflectCtx funcSigs globalTypes memTypes tableLimits (length m.dataSegments) of
        SomeModuleShape ctxS@(SModuleShape ftsS gsS msS tsS _) -> do
            functions <- elaborateFuncs ctxS (m.types) ftsS (map Left m.imports ++ map Right m.functions)
            globals <- elaborateGlobals gsS (m.globals)
            dataSegments <- traverse (elaborateData (memsNonEmpty msS)) (zip [0 ..] m.dataSegments)
            elementSegments <- traverse (elaborateElements ftsS (tablesNonEmpty tsS)) (zip [0 ..] m.elementSegments)
            start <- traverse (resolveStart ftsS) (m.start)
            Right (SomeModule ctxS (Module {functions, globals, dataSegments, elementSegments, exports = m.exports, start}))
  where
    tableLimits = [t.limits | t <- m.tables]
    -- The function index space: imports first, then the module's own functions.
    funcSigs = [ft | RawImport _ _ (ImportFunc ft) <- m.imports] ++ map (\(RawFunction sig _ _) -> sig) (m.functions)
    globalTypes = map (\(RawGlobal gt _) -> gt) (m.globals)
    memTypes = map (\(RawMemory mt) -> mt) (m.memories)

{- | The module-level rules of the validation section that need no shape: well-formed,
  bounded memory limits; at most one memory; distinct export names; export indices within
  their index spaces.
-}
validateStructure :: RawModule -> Either ElabError ()
validateStructure m = do
    mapM_ checkLimits [declared | RawMemory (MemType _ declared) <- m.memories]
    when (length m.memories > 1) (Left TooManyMemories)
    mapM_ checkTableLimits [t.limits | t <- m.tables]
    checkDistinct [e.name | e <- m.exports]
    mapM_ checkExport m.exports
  where
    checkLimits declared
        | declared.min > maxMemoryPages = Left (InvalidMemoryLimits declared)
        | Just hi <- declared.max, hi > maxMemoryPages || declared.min > hi = Left (InvalidMemoryLimits declared)
        | otherwise = Right ()
    checkTableLimits declared
        | Just hi <- declared.max, declared.min > hi = Left (InvalidTableLimits declared)
        | otherwise = Right ()
    checkDistinct names = case [n | (k, n) <- zip [0 :: Int ..] names, n `elem` take k names] of
        [] -> Right ()
        n : _ -> Left (DuplicateExport n)
    checkExport (Export _ desc) = case desc of
        ExportFunc (FunctionIdx i) -> inRange Functions i (length m.imports + length m.functions)
        ExportGlobal (GlobalIdx i) -> inRange Globals i (length m.globals)
        ExportMem (MemoryIdx i) -> inRange Memories i (length m.memories)
        ExportTable (TableIdx i) -> inRange Tables i (length m.tables)
    inRange space i count
        | fromIntegral i < count = Right ()
        | otherwise = Left (IndexOutOfRange space i)

-- | The start function must exist and take and return nothing.
resolveStart :: Sing (fts :: [FuncType]) -> FunctionIdx -> Either ElabError (Elem ('FuncType '[] '[]) fts)
resolveStart ftsS (FunctionIdx idx) = do
    SomeFuncRef psS rsS funcIx <- note (IndexOutOfRange Functions idx) (lookupFuncRef ftsS idx)
    Refl <- note InvalidStartFunction (decideEquality psS SNil)
    Refl <- note InvalidStartFunction (decideEquality rsS SNil)
    Right funcIx

{- | The functions, one per entry of the index space: an import is kept by name (linking is
  instantiation's job), a defined function is elaborated.
-}
elaborateFuncs ::
    SModuleShape shape ->
    [FuncType] ->
    Sing fts ->
    [Either RawImport RawFunction] ->
    Either ElabError (FunctionSpace shape fts)
elaborateFuncs _ _ SNil [] = Right NoFunctions
elaborateFuncs ctxS types (SCons ft fs) (entry : rest) = do
    fs' <- elaborateFuncs ctxS types fs rest
    case entry of
        Left (RawImport moduleName fieldName (ImportFunc _)) -> Right (Imported moduleName fieldName fs')
        Right f -> (`Defined` fs') <$> elaborateFunctionIn ctxS types ft f
elaborateFuncs _ _ _ _ = Left (Malformed "function/signature count mismatch")

elaborateFunctionIn ::
    SModuleShape shape ->
    [FuncType] ->
    SFuncType ft ->
    RawFunction ->
    Either ElabError (Function shape ft)
elaborateFunctionIn ctxS types (SFuncType psS rsS) (RawFunction _ declaredT body) =
    case reflectStack declaredT of
        SomeStack declS ->
            let env = ElabEnv ctxS types rsS (sReverseOnto psS declS) (SCons rsS SNil)
             in do
                    elaborated <- elabSeq env SNil body
                    case elaborated of
                        Reachable soS bodySeq -> do
                            Refl <- note (ResultMismatch (stackToList rsS) (stackToList soS)) (decideEquality soS rsS)
                            Right (Function psS declS bodySeq)
                        Diverged final poly -> do
                            checkDeadResult final rsS
                            Right (Function psS declS poly)

elaborateGlobals :: Sing gs -> [RawGlobal] -> Either ElabError (GlobalSpace gs)
elaborateGlobals = go 0
  where
    go :: Word32 -> Sing gs -> [RawGlobal] -> Either ElabError (GlobalSpace gs)
    go _ SNil [] = Right NoGlobals
    go index (SCons (SGlobalType _ sn) gs) (RawGlobal _ initExpr : rest) = do
        value <- evalConstInit (InvalidGlobalInitializer index) sn initExpr
        rest' <- go (index + 1) gs rest
        Right (Declared (Global value) rest')
    go _ _ _ = Left (Malformed "global/type count mismatch")

-- | A constant expression of the given type: exactly one constant instruction.
evalConstInit :: ElabError -> Sing (n :: ValType) -> [RawInstr] -> Either ElabError (HostType n)
evalConstInit invalid sn [Const st literal] = case decideEquality st sn of
    Just Refl -> Right literal
    Nothing -> Left invalid
evalConstInit invalid _ _ = Left invalid

-- | An active data segment needs a memory to land in and a constant @i32@ offset.
elaborateData :: Maybe (NonEmptyMems ms) -> (Int, RawDataSegment) -> Either ElabError DataSegment
elaborateData mems (index, RawDataSegment mode bytes) = case mode of
    Passive -> Right (DataSegment Nothing bytes)
    Active offsetExpr -> do
        NonEmptyMems <- note (NoMemory "data") mems
        offset <- evalConstInit (InvalidDataSegmentOffset index) SI32 offsetExpr
        Right (DataSegment (Just offset) bytes)

{- | An element segment needs a table to land in, a constant @i32@ offset, and functions that
  exist: each index is resolved to a typed reference ('SomeFuncRef'), so a table only ever
  holds real functions.
-}
elaborateElements :: Sing (fts :: [FuncType]) -> Maybe (NonEmptyTables ts) -> (Int, RawElementSegment) -> Either ElabError (ElementSegment fts)
elaborateElements ftsS tables (index, RawElementSegment offsetExpr functions) = do
    NonEmptyTables <- note (NoTable "elem") tables
    offset <- evalConstInit (InvalidElementSegmentOffset index) SI32 offsetExpr
    refs <- traverse (\(FunctionIdx f) -> note (IndexOutOfRange Functions f) (lookupFuncRef ftsS f)) functions
    Right (ElementSegment offset refs)
