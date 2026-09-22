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
    elaborateModuleWith,
) where

import Control.Monad (foldM, when)
import Data.Bifunctor (first)
import Data.Text (Text)
import Data.Type.Equality ((:~:) (Refl))
import Data.Word (Word32)

import Data.List.Singletons ((%++))
import Data.Maybe (fromMaybe)
import Data.Singletons (SomeSing (..), toSing, withSomeSing)
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
import Syntax.TypesIFC
import Validation.Policy (Assembled (..), Policy, PolicyError, assemble, emptyPolicy, mergePolicies, sectionPolicy)
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
    | {- | information may not flow this way: the instruction, the level it comes from, the level
      it would flow into
      -}
      IllegalFlow Text SecLevel SecLevel
    | -- | a level annotation on an instruction that takes none
      AnnotationMisplaced
    | -- | @declassify@ in a module whose policy does not allow it
      DeclassifyNotAllowed
    | -- | the security policy could not be read or does not fit the module
      BadPolicy PolicyError
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
data ElabEnv (shape :: ModuleShape) (ret :: LResultType) (locals :: [LValType]) (labels :: [LResultType]) = ElabEnv
    { shape :: Sing shape
    , types :: [FuncType]
    -- ^ the module's type section, which @call_indirect@ refers into
    , results :: Sing ret
    , locals :: Sing locals
    , labels :: Sing labels
    , loadDefault :: SecLevel
    -- ^ the level a load declares when nothing annotates it (see "Validation.Policy")
    , declassifyAllowed :: Bool
    -- ^ whether the policy enables 'Declassify'
    }

{- | The result of elaborating a whole instruction sequence that started from pc stack @pcIn@
  and stack @stackIn@. It always says where the pc stack ended up (and that it kept its length,
  see 'SameLength'). A sequence either runs to its end or leaves early through an unconditional
  branch, and the two cases carry different evidence:
-}
data ElaboratedExpr (shape :: ModuleShape) (ret :: LResultType) (locals :: [LValType]) (labels :: [LResultType]) (pcIn :: PcStack) (stackIn :: [LValType]) where
    -- | Control reached the end of the sequence, leaving a concrete @stackOut@ on top.
    Reachable ::
        SameLength pcIn pcOut ->
        Sing pcOut ->
        Sing stackOut ->
        Expr shape ('FrameShape locals ret) labels pcIn pcOut stackIn stackOut ->
        ElaboratedExpr shape ret locals labels pcIn stackIn
    {- | The sequence ended in an unconditional transfer (@br@ / @return@ / @unreachable@), so
    control never falls out the bottom. Nothing constrains the output stack, so it is left
    universally quantified — exactly the spec's stack-polymorphism for dead code. The
    'PolyStack' is what the dead tail leaves, still to be checked against the expected result.
    -}
    Diverged ::
        SameLength pcIn pcOut ->
        Sing pcOut ->
        PolyStack ->
        (forall stackOut. Expr shape ('FrameShape locals ret) labels pcIn pcOut stackIn stackOut) ->
        ElaboratedExpr shape ret locals labels pcIn stackIn

{- | The result of elaborating a single instruction — the per-instruction version of
  'ElaboratedExpr', with the same two cases. 'elabSeq' folds these into an 'ElaboratedExpr'
  as it walks the sequence.
-}
data ElaboratedInstr (shape :: ModuleShape) (ret :: LResultType) (locals :: [LValType]) (labels :: [LResultType]) (pcIn :: PcStack) (stackIn :: [LValType]) where
    {- | An ordinary instruction: it leaves a concrete @stackOut@ and elaboration continues
    from there (the analogue of 'Reachable').
    -}
    Produces ::
        SameLength pcIn pcOut ->
        Sing pcOut ->
        Sing stackOut ->
        Instr shape ('FrameShape locals ret) labels pcIn pcOut stackIn stackOut ->
        ElaboratedInstr shape ret locals labels pcIn stackIn
    {- | An unconditional transfer (@br@ / @return@ / @unreachable@): control leaves here, so any
    instructions after it are dead code and the output stack is unconstrained (the analogue
    of 'Diverged').
    -}
    Transfers ::
        SameLength pcIn pcOut ->
        Sing pcOut ->
        (forall stackOut. Instr shape ('FrameShape locals ret) labels pcIn pcOut stackIn stackOut) ->
        ElaboratedInstr shape ret locals labels pcIn stackIn

note :: ElabError -> Maybe a -> Either ElabError a
note e = maybe (Left e) Right

-- | Require that level @from@ may flow into level @into@, or report the instruction.
requireFlow :: Text -> Sing (from :: SecLevel) -> Sing (into :: SecLevel) -> Either ElabError (FlowsInto from into)
requireFlow name from into = note (IllegalFlow name (fromSing from) (fromSing into)) (decideFlow from into)

-- | Require that the values a branch carries are at least as secret as the decision to branch.
requireCarried :: Text -> Sing (l :: SecLevel) -> Sing (rs :: [LValType]) -> Either ElabError (AllAtLeast l rs)
requireCarried name l rs = note (IllegalFlow name (fromSing l) Low) (decideAllAtLeast l rs)

-- *** Sequences ***

elabSeq ::
    ElabEnv shape ret locals labels ->
    Sing (pc ': pcs) ->
    Sing stackIn ->
    [RawInstr] ->
    Either ElabError (ElaboratedExpr shape ret locals labels (pc ': pcs) stackIn)
elabSeq _ pcs stackIn [] = Right (Reachable (sameLengthAs pcs) pcs stackIn INil)
elabSeq env pcs stackIn (raw : rest) = do
    elaboratedInstr <- elabInstr env pcs stackIn raw
    case elaboratedInstr of
        Produces same@(BothLonger _) pcs'@(SCons _ _) stackOut instr -> do
            rest' <- elabSeq env pcs' stackOut rest
            pure $ case rest' of
                Reachable same' pcOut stackOut' seq' -> Reachable (thenSameLength same same') pcOut stackOut' (instr :. seq')
                Diverged same' pcOut final poly -> Diverged (thenSameLength same same') pcOut final (instr :. poly)
        Transfers same pcOut transfer -> do
            final <- validateDead env pcs rest
            pure (Diverged same pcOut final (transfer :. INil))

-- *** Single instructions ***

elabInstr ::
    forall shape ret locals labels pc pcs stackIn.
    ElabEnv shape ret locals labels ->
    Sing (pc ': pcs) ->
    Sing stackIn ->
    RawInstr ->
    Either ElabError (ElaboratedInstr shape ret locals labels (pc ': pcs) stackIn)
elabInstr env pcsIn@(SCons pc _) stackIn instr = case instr of
    {- Constants -}
    Const st literal -> do
        isNum <- requireNum st
        Right (Produces (sameLengthAs pcsIn) pcsIn (SCons (st :%~ sJoin pc SLow) stackIn) (IConst @'Low isNum literal))
    {- Numeric (consume two of type t, produce one of type t) -}
    Add st -> do
        isNum <- requireNum st
        consumeTwo st st pcsIn stackIn (IAdd isNum)
    Sub st -> do
        isNum <- requireNum st
        consumeTwo st st pcsIn stackIn (ISub isNum)
    Mul st -> do
        isNum <- requireNum st
        consumeTwo st st pcsIn stackIn (IMul isNum)
    Div st sign -> do
        sn <- requireNumWithSign st sign
        consumeTwo st st pcsIn stackIn (IDiv sn)
    Rem st sign -> do
        isInt <- requireInt st
        consumeTwo st st pcsIn stackIn (IRem isInt sign)
    {- Comparison (consume two of type t, produce one i32). @eqz@ is integer-only. -}
    Eq st -> do
        isNum <- requireNum st
        consumeTwo st SI32 pcsIn stackIn (IEq isNum)
    Ne st -> do
        isNum <- requireNum st
        consumeTwo st SI32 pcsIn stackIn (INe isNum)
    Lt st sign -> do
        sn <- requireNumWithSign st sign
        consumeTwo st SI32 pcsIn stackIn (ILt sn)
    Gt st sign -> do
        sn <- requireNumWithSign st sign
        consumeTwo st SI32 pcsIn stackIn (IGt sn)
    Le st sign -> do
        sn <- requireNumWithSign st sign
        consumeTwo st SI32 pcsIn stackIn (ILe sn)
    Ge st sign -> do
        sn <- requireNumWithSign st sign
        consumeTwo st SI32 pcsIn stackIn (IGe sn)
    Eqz st -> case stackIn of
        SCons (sa :%~ la) rest -> do
            isInt <- requireInt st
            Refl <- note (OperandMismatch "eqz" (valTypeOf st) (valTypeOf sa)) (decideEquality sa st)
            Right (Produces (sameLengthAs pcsIn) pcsIn (SCons (SI32 :%~ sJoin pc la) rest) (IEqz isInt))
        _ -> Left (StackUnderflow "eqz")
    {- Stack management -}
    Drop -> case stackIn of
        SCons _ rest -> Right (Produces (sameLengthAs pcsIn) pcsIn rest IDrop)
        _ -> Left (StackUnderflow "drop")
    Select -> elabSelect Nothing pcsIn stackIn
    SelectTyped [t] -> elabSelect (Just t) pcsIn stackIn
    SelectTyped ts -> Left (InvalidSelectArity (length ts))
    {- Locals -}
    LocalGet (LocalIdx i) -> case mkLocalElem (env.locals) i of
        Just (SomeElem sv@(svt :%~ lvar) ix) -> Right (Produces (sameLengthAs pcsIn) pcsIn (SCons (svt :%~ sJoin pc lvar) stackIn) (ILocalGet (resolveLocal sv ix)))
        Nothing -> Left (IndexOutOfRange Locals i)
    LocalSet (LocalIdx i) -> case mkLocalElem (env.locals) i of
        Just (SomeElem sv@(svt :%~ lvar) ix) -> case stackIn of
            SCons (stop :%~ lv) rest -> do
                Refl <- note (OperandMismatch "local.set" (valTypeOf svt) (valTypeOf stop)) (decideEquality stop svt)
                pcFlows <- requireFlow "local.set" pc lvar
                valueFlows <- requireFlow "local.set" lv lvar
                Right (Produces (sameLengthAs pcsIn) pcsIn rest (ILocalSet pcFlows valueFlows (resolveLocal sv ix)))
            _ -> Left (StackUnderflow "local.set")
        Nothing -> Left (IndexOutOfRange Locals i)
    LocalTee (LocalIdx i) -> case mkLocalElem (env.locals) i of
        Just (SomeElem sv@(svt :%~ lvar) ix) -> case stackIn of
            SCons (stop :%~ lv) _ -> do
                Refl <- note (OperandMismatch "local.tee" (valTypeOf svt) (valTypeOf stop)) (decideEquality stop svt)
                pcFlows <- requireFlow "local.tee" pc lvar
                valueFlows <- requireFlow "local.tee" lv lvar
                Right (Produces (sameLengthAs pcsIn) pcsIn stackIn (ILocalTee pcFlows valueFlows (resolveLocal sv ix)))
            _ -> Left (StackUnderflow "local.tee")
        Nothing -> Left (IndexOutOfRange Locals i)
    {- Globals -}
    GlobalGet (GlobalIdx g) -> case lookupGlobalRef (globalTypesSing (env.shape)) g of
        Nothing -> Left (IndexOutOfRange Globals g)
        Just (SomeGlobalRef _ (st :%~ lvar) gix) -> Right (Produces (sameLengthAs pcsIn) pcsIn (SCons (st :%~ sJoin pc lvar) stackIn) (IGlobalGet gix))
    GlobalSet (GlobalIdx g) -> case lookupGlobalRef (globalTypesSing (env.shape)) g of
        Nothing -> Left (IndexOutOfRange Globals g)
        Just (SomeGlobalRef smut (st :%~ lvar) gix) -> case smut of
            SImmutable -> Left (ImmutableGlobal g)
            SMutable -> case stackIn of
                SCons (stop :%~ lv) rest -> do
                    Refl <- note (OperandMismatch "global.set" (valTypeOf st) (valTypeOf stop)) (decideEquality stop st)
                    pcFlows <- requireFlow "global.set" pc lvar
                    valueFlows <- requireFlow "global.set" lv lvar
                    Right (Produces (sameLengthAs pcsIn) pcsIn rest (IGlobalSet pcFlows valueFlows gix))
                _ -> Left (StackUnderflow "global.set")
    {- Memory -}
    Load st memArg -> elabMemory env pcsIn stackIn Nothing (Load st memArg)
    Store st memArg -> elabMemory env pcsIn stackIn Nothing (Store st memArg)
    LoadN st width sign memArg -> elabMemory env pcsIn stackIn Nothing (LoadN st width sign memArg)
    StoreN st width memArg -> elabMemory env pcsIn stackIn Nothing (StoreN st width memArg)
    Annotated level access -> elabMemory env pcsIn stackIn (Just level) access
    MemorySize -> do
        NonEmptyMems <- requireMemory env "memory.size"
        Right (Produces (sameLengthAs pcsIn) pcsIn (SCons (SI32 :%~ pc) stackIn) IMemSize)
    MemoryCopy -> do
        NonEmptyMems <- requireMemory env "memory.copy"
        threeAddresses "memory.copy" stackIn pcsIn IMemCopy
    MemoryFill -> do
        NonEmptyMems <- requireMemory env "memory.fill"
        threeAddresses "memory.fill" stackIn pcsIn IMemFill
    MemoryInit (DataIdx d) -> do
        NonEmptyMems <- requireMemory env "memory.init"
        segmentIx <- note (IndexOutOfRange DataSegments d) (mkDataElem (dataShapesSing (env.shape)) d)
        threeAddresses "memory.init" stackIn pcsIn (`IMemInit` segmentIx)
    Relabel target -> case stackIn of
        SCons (sv :%~ lv) rest -> withSomeSing target $ \starget -> do
            flows <- requireFlow "relabel" lv starget
            Right (Produces (sameLengthAs pcsIn) pcsIn (SCons (sv :%~ starget) rest) (IRelabel flows))
        _ -> Left (StackUnderflow "relabel")
    Declassify target -> case stackIn of
        SCons (sv :%~ _) rest
            | env.declassifyAllowed -> withSomeSing target $ \starget -> Right (Produces (sameLengthAs pcsIn) pcsIn (SCons (sv :%~ starget) rest) IDeclassify)
            | otherwise -> Left DeclassifyNotAllowed
        _ -> Left (StackUnderflow "declassify")
    DataDrop (DataIdx d) -> do
        segmentIx <- note (IndexOutOfRange DataSegments d) (mkDataElem (dataShapesSing (env.shape)) d)
        Right (Produces (sameLengthAs pcsIn) pcsIn stackIn (IDataDrop segmentIx))
    MemoryGrow -> case stackIn of
        SCons (sc :%~ lc) rest -> do
            NonEmptyMems <- requireMemory env "memory.grow"
            Refl <- note (OperandMismatch "memory.grow" I32 (valTypeOf sc)) (decideEquality sc SI32)
            publicContext <- requireFlow "memory.grow" (sJoin pc lc) SLow
            Right (Produces (sameLengthAs pcsIn) pcsIn (SCons (SI32 :%~ pc) rest) (IMemGrow publicContext))
        _ -> Left (StackUnderflow "memory.grow")
    {- Calls -}
    CallIndirect (TypeIdx t) -> case stackIn of
        SCons (sc :%~ lidx) rest -> do
            NonEmptyTables <- requireTable env
            Refl <- note (OperandMismatch "call_indirect" I32 (valTypeOf sc)) (decideEquality sc SI32)
            publicContext <- requireFlow "call_indirect" (sJoin pc lidx) SLow
            expected <- note (IndexOutOfRange Types t) (nth (env.types) t)
            case toSing (publicFuncType (stackOrderFuncType expected)) of
                SomeSing (SFuncType psS rsS) -> case matchPrefix psS rest of
                    Nothing -> Left (StackMismatch "call_indirect" (stackToList psS) (stackToList rest))
                    Just (SomeSplit sS witness) -> Right (Produces (sameLengthAs pcsIn) pcsIn (rsS %++ sS) (ICallIndirect publicContext witness (SFuncType psS rsS)))
        _ -> Left (StackUnderflow "call_indirect")
    Call (FunctionIdx f) -> case lookupFuncRef (funcTypesSing (env.shape)) f of
        Nothing -> Left (IndexOutOfRange Functions f)
        Just (SomeFuncRef psS rsS fix) -> case matchPrefix psS stackIn of
            Nothing -> Left (StackMismatch "call" (stackToList psS) (stackToList stackIn))
            Just (SomeSplit sS witness) -> do
                publicContext <- requireFlow "call" pc SLow
                Right (Produces (sameLengthAs pcsIn) pcsIn (rsS %++ sS) (ICall publicContext witness fix))
    {- Integer bitwise / shift / count (integer types only) -}
    And st -> do
        isInt <- requireInt st
        sameTypeBinary st pcsIn stackIn (IBitwise isInt BwAnd)
    Or st -> do
        isInt <- requireInt st
        sameTypeBinary st pcsIn stackIn (IBitwise isInt BwOr)
    Xor st -> do
        isInt <- requireInt st
        sameTypeBinary st pcsIn stackIn (IBitwise isInt BwXor)
    Shl st -> do
        isInt <- requireInt st
        sameTypeBinary st pcsIn stackIn (IBitwise isInt BwShl)
    Shr st sign -> do
        isInt <- requireInt st
        sameTypeBinary st pcsIn stackIn (IBitwise isInt (BwShr sign))
    Rotl st -> do
        isInt <- requireInt st
        sameTypeBinary st pcsIn stackIn (IBitwise isInt BwRotl)
    Rotr st -> do
        isInt <- requireInt st
        sameTypeBinary st pcsIn stackIn (IBitwise isInt BwRotr)
    Clz st -> do
        isInt <- requireInt st
        sameTypeUnary st pcsIn stackIn (ICount isInt OpClz)
    Ctz st -> do
        isInt <- requireInt st
        sameTypeUnary st pcsIn stackIn (ICount isInt OpCtz)
    Popcnt st -> do
        isInt <- requireInt st
        sameTypeUnary st pcsIn stackIn (ICount isInt OpPopcnt)
    {- Floating-point unary / binary (floating-point types only) -}
    Abs st -> do
        isFloat <- requireFloat st
        sameTypeUnary st pcsIn stackIn (IFloatUn isFloat FAbs)
    Neg st -> do
        isFloat <- requireFloat st
        sameTypeUnary st pcsIn stackIn (IFloatUn isFloat FNeg)
    Sqrt st -> do
        isFloat <- requireFloat st
        sameTypeUnary st pcsIn stackIn (IFloatUn isFloat FSqrt)
    Ceil st -> do
        isFloat <- requireFloat st
        sameTypeUnary st pcsIn stackIn (IFloatUn isFloat FCeil)
    Floor st -> do
        isFloat <- requireFloat st
        sameTypeUnary st pcsIn stackIn (IFloatUn isFloat FFloor)
    FloatTrunc st -> do
        isFloat <- requireFloat st
        sameTypeUnary st pcsIn stackIn (IFloatUn isFloat FTrunc)
    Nearest st -> do
        isFloat <- requireFloat st
        sameTypeUnary st pcsIn stackIn (IFloatUn isFloat FNearest)
    Min st -> do
        isFloat <- requireFloat st
        sameTypeBinary st pcsIn stackIn (IFloatBin isFloat FMin)
    Max st -> do
        isFloat <- requireFloat st
        sameTypeBinary st pcsIn stackIn (IFloatBin isFloat FMax)
    Copysign st -> do
        isFloat <- requireFloat st
        sameTypeBinary st pcsIn stackIn (IFloatBin isFloat FCopysign)
    {- Conversions: the opcode's own type indices are the source/result -}
    Convert op ->
        let (nf, nt) = convertEnds op
         in case stackIn of
                SCons (sa :%~ la) rest -> do
                    Refl <- note (OperandMismatch "conversion" (fromSing (numSing nf)) (valTypeOf sa)) (decideEquality sa (numSing nf))
                    Right (Produces (sameLengthAs pcsIn) pcsIn (SCons (numSing nt :%~ sJoin pc la) rest) (IConvert op))
                _ -> Left (StackUnderflow "conversion")
    {- Inert -}
    Nop -> Right (Produces (sameLengthAs pcsIn) pcsIn stackIn INop)
    {- Structured control -}
    Block (FuncType psT rsT) body ->
        case (reflectStack (stackOrder psT), reflectStack (stackOrder rsT)) of
            (SomeStack psS, SomeStack rsS) -> case matchPrefix psS stackIn of
                Nothing -> Left (StackMismatch "block" (stackToList psS) (stackToList stackIn))
                Just (SomeSplit sS witness) ->
                    elabBodyChecked (pushLabel rsS env) (SCons pc pcsIn) psS rsS body $ \(BodyResult (BothLonger same) (SCons _ pcsOut) bodySeq) ->
                        Right (Produces same pcsOut (rsS %++ sS) (IBlock witness bodySeq))
    Loop (FuncType psT rsT) body ->
        case (reflectStack (stackOrder psT), reflectStack (stackOrder rsT)) of
            (SomeStack psS, SomeStack rsS) -> case matchPrefix psS stackIn of
                Nothing -> Left (StackMismatch "loop" (stackToList psS) (stackToList stackIn))
                Just (SomeSplit sS witness) -> loopAt pc $ \pcLoop entryFlows ->
                    elabBodyChecked (pushLabel psS env) (SCons pcLoop pcsIn) psS rsS body $ \(BodyResult (BothLonger same) (SCons pcBody pcsOut) bodySeq) -> do
                        backFlows <- requireFlow "loop" pcBody pcLoop
                        Right (Produces same pcsOut (rsS %++ sS) (ILoop entryFlows backFlows witness bodySeq))
    If (FuncType psT rsT) thenBody elseBody -> case stackIn of
        SCons (sc :%~ lc) rest -> do
            Refl <- note (OperandMismatch "if" I32 (valTypeOf sc)) (decideEquality sc SI32)
            case (reflectStack (stackOrder psT), reflectStack (stackOrder rsT)) of
                (SomeStack psS, SomeStack rsS) -> case matchPrefix psS rest of
                    Nothing -> Left (StackMismatch "if" (stackToList psS) (stackToList rest))
                    Just (SomeSplit sS witness) ->
                        elabBodyChecked (pushLabel rsS env) (SCons (sJoin pc lc) pcsIn) psS rsS thenBody $ \(BodyResult (BothLonger sameThen) (SCons _ pcsThen) thenSeq) ->
                            elabBodyChecked (pushLabel rsS env) (SCons (sJoin pc lc) pcsIn) psS rsS elseBody $ \(BodyResult (BothLonger sameElse) (SCons _ pcsElse) elseSeq) ->
                                Right (Produces (joinEachSameLength sameThen sameElse) (sJoinEach pcsThen pcsElse) (rsS %++ sS) (IIf witness thenSeq elseSeq))
        _ -> Left (StackUnderflow "if")
    {- Branches (unconditional ones diverge) -}
    Br (LabelIdx l) -> case mkBranchTarget pc (env.labels) pcsIn l of
        Nothing -> Left (IndexOutOfRange Labels l)
        Just (SomeBranchTarget rsS pcsOut same target) -> case matchPrefix rsS stackIn of
            Nothing -> Left (StackMismatch "br" (stackToList rsS) (stackToList stackIn))
            Just (SomeSplit _ witness) -> do
                carried <- requireCarried "br" pc rsS
                Right (Transfers same pcsOut (IBr carried witness target))
    BrIf (LabelIdx l) -> case stackIn of
        SCons (sc :%~ lc) rest -> do
            Refl <- note (OperandMismatch "br_if" I32 (valTypeOf sc)) (decideEquality sc SI32)
            case mkBranchTarget (sJoin pc lc) (env.labels) pcsIn l of
                Nothing -> Left (IndexOutOfRange Labels l)
                Just (SomeBranchTarget rsS pcsOut same target) -> case matchPrefix rsS rest of
                    Nothing -> Left (StackMismatch "br_if" (stackToList rsS) (stackToList rest))
                    Just (SomeSplit _ witness) -> do
                        carried <- requireCarried "br_if" (sJoin pc lc) rsS
                        Right (Produces same pcsOut rest (IBrIf carried witness target))
        _ -> Left (StackUnderflow "br_if")
    BrTable targets (LabelIdx d) -> case stackIn of
        SCons (sc :%~ lc) rest -> case decideEquality sc SI32 of
            Nothing -> Left (OperandMismatch "br_table" I32 (valTypeOf sc))
            Just Refl -> case mkLabelElem (env.labels) d of
                Nothing -> Left (IndexOutOfRange Labels d)
                Just (SomeLabel rsS defIx) -> case mapM (resolveTarget env rsS) targets of
                    Left err -> Left err
                    Right targetIxs -> case matchPrefix rsS rest of
                        Nothing -> Left (StackMismatch "br_table" (stackToList rsS) (stackToList rest))
                        Just (SomeSplit _ witness) -> do
                            carried <- requireCarried "br_table" (sJoin pc lc) rsS
                            Right (Transfers (raiseAllSameLength (sJoin pc lc) pcsIn) (sRaiseAll (sJoin pc lc) pcsIn) (IBrTable carried witness targetIxs defIx))
        _ -> Left (StackUnderflow "br_table")
    Return -> case matchPrefix (env.results) stackIn of
        Nothing -> Left (StackMismatch "return" (stackToList (env.results)) (stackToList stackIn))
        Just (SomeSplit _ witness) -> do
            carried <- requireCarried "return" pc (env.results)
            Right (Transfers (raiseAllSameLength pc pcsIn) (sRaiseAll pc pcsIn) (IReturn carried witness))
    Unreachable -> Right (Transfers (sameLengthAs pcsIn) pcsIn IUnreachable)

-- | Push a label's result type onto the elaboration environment's label context.

{- | @select@ takes a condition over two operands of one numeric type; the typed form also
  names that type, which the operands must have.
-}
elabSelect :: Maybe ValType -> Sing (pc ': pcs) -> Sing stackIn -> Either ElabError (ElaboratedInstr shape ret locals labels (pc ': pcs) stackIn)
elabSelect annotation pcsIn@(SCons pc _) stackIn = case stackIn of
    SCons (sc :%~ lc) (SCons (va :%~ l1) (SCons (vb :%~ l2) rest)) -> do
        Refl <- note (OperandMismatch "select" I32 (valTypeOf sc)) (decideEquality sc SI32)
        Refl <- note (OperandMismatch "select" (valTypeOf va) (valTypeOf vb)) (decideEquality va vb)
        mapM_ (\t -> if t == valTypeOf va then Right () else Left (OperandMismatch "select" t (valTypeOf va))) annotation
        isNum <- requireNum va
        Right (Produces (sameLengthAs pcsIn) pcsIn (SCons (va :%~ sJoin pc (sJoin lc (sJoin l1 l2))) rest) (ISelect isNum))
    _ -> Left (StackUnderflow "select")

pushLabel :: Sing rs -> ElabEnv shape ret locals labels -> ElabEnv shape ret locals (rs ': labels)
pushLabel rsS env = env {labels = SCons rsS (env.labels)}

{- | What a body left behind: the pc stack (with the proof it kept its length) and the typed
  sequence, which produces @rs@ from @ps@.
-}
data BodyResult shape locals ret labels pcIn ps rs where
    BodyResult ::
        SameLength pcIn pcOut ->
        Sing pcOut ->
        Expr shape ('FrameShape locals ret) labels pcIn pcOut ps rs ->
        BodyResult shape locals ret labels pcIn ps rs

{- | Elaborate a block/loop/if body (its label already pushed onto @env@, its pc entry pushed
  onto the pc stack), checking it transforms @ps@ into @rs@, and hand the result to the
  continuation.
-}
elabBodyChecked ::
    ElabEnv shape ret locals labels ->
    Sing (pc ': pcs) ->
    Sing ps ->
    Sing rs ->
    [RawInstr] ->
    (BodyResult shape locals ret labels (pc ': pcs) ps rs -> Either ElabError a) ->
    Either ElabError a
elabBodyChecked env pcsIn psS rsS body k = do
    body' <- elabSeq env pcsIn psS body
    case body' of
        Reachable same pcsOut soS seq' -> do
            Refl <- note (ResultMismatch (stackToList rsS) (stackToList soS)) (decideEquality soS rsS)
            k (BodyResult same pcsOut seq')
        Diverged same pcsOut final poly -> do
            checkDeadResult final rsS
            k (BodyResult same pcsOut poly)

{- | The pc a loop body is checked at: the current pc if the body keeps it, and 'High if a
  branch inside raises it, because the body may run again under what it left. With two levels
  the second attempt always succeeds, so this is a fixed point in at most two steps.
-}
loopAt :: Sing (pc :: SecLevel) -> (forall pcLoop. Sing pcLoop -> FlowsInto pc pcLoop -> Either ElabError a) -> Either ElabError a
loopAt pc k = case k pc (case pc of SLow -> LowFlowsAnywhere; SHigh -> HighFlowsToHigh) of
    Right a -> Right a
    Left _ -> k SHigh (case pc of SLow -> LowFlowsAnywhere; SHigh -> HighFlowsToHigh)

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

{- | The four memory accesses, with the level they declare: the annotation if there is one,
  otherwise the policy's default for a load and, for a store, the lowest level the rule allows
  (the join of the pc, the address and the value), which is always sound. An annotation on any
  other instruction is a mistake of the policy stage.
-}
elabMemory ::
    forall shape ret locals labels pc pcs stackIn.
    ElabEnv shape ret locals labels ->
    Sing (pc ': pcs) ->
    Sing stackIn ->
    Maybe SecLevel ->
    RawInstr ->
    Either ElabError (ElaboratedInstr shape ret locals labels (pc ': pcs) stackIn)
elabMemory env pcsIn@(SCons pc _) stackIn annotation access = case access of
    Load st memArg -> case stackIn of
        SCons (sc :%~ la) rest -> do
            NonEmptyMems <- requireMemory env "load"
            isNum <- requireNum st
            Refl <- note (OperandMismatch "load" I32 (valTypeOf sc)) (decideEquality sc SI32)
            checkAlign memArg (numBytes isNum)
            withSomeSing loadLevel $ \level ->
                Right (Produces (sameLengthAs pcsIn) pcsIn (SCons (st :%~ sJoin pc (sJoin la level)) rest) (ILoad level isNum memArg))
        _ -> Left (StackUnderflow "load")
    LoadN st width sign memArg -> case stackIn of
        SCons (sc :%~ la) rest -> do
            NonEmptyMems <- requireMemory env "load"
            nw <- requireNarrow st width
            Refl <- note (OperandMismatch "load" I32 (valTypeOf sc)) (decideEquality sc SI32)
            checkAlign memArg (narrowBytes nw)
            withSomeSing loadLevel $ \level ->
                Right (Produces (sameLengthAs pcsIn) pcsIn (SCons (st :%~ sJoin pc (sJoin la level)) rest) (ILoadN level nw sign memArg))
        _ -> Left (StackUnderflow "load")
    Store st memArg -> case stackIn of
        SCons (sv :%~ lv) (SCons (sc :%~ la) rest) -> do
            NonEmptyMems <- requireMemory env "store"
            isNum <- requireNum st
            Refl <- note (OperandMismatch "store" (valTypeOf st) (valTypeOf sv)) (decideEquality sv st)
            Refl <- note (OperandMismatch "store" I32 (valTypeOf sc)) (decideEquality sc SI32)
            checkAlign memArg (numBytes isNum)
            storeAt (sJoin pc (sJoin la lv)) $ \level flows ->
                Right (Produces (sameLengthAs pcsIn) pcsIn rest (IStore level flows isNum memArg))
        _ -> Left (StackUnderflow "store")
    StoreN st width memArg -> case stackIn of
        SCons (sv :%~ lv) (SCons (sc :%~ la) rest) -> do
            NonEmptyMems <- requireMemory env "store"
            nw <- requireNarrow st width
            Refl <- note (OperandMismatch "store" (valTypeOf st) (valTypeOf sv)) (decideEquality sv st)
            Refl <- note (OperandMismatch "store" I32 (valTypeOf sc)) (decideEquality sc SI32)
            checkAlign memArg (narrowBytes nw)
            storeAt (sJoin pc (sJoin la lv)) $ \level flows ->
                Right (Produces (sameLengthAs pcsIn) pcsIn rest (IStoreN level flows nw memArg))
        _ -> Left (StackUnderflow "store")
    _ -> Left AnnotationMisplaced
  where
    loadLevel = fromMaybe env.loadDefault annotation
    -- The level a store declares, with the proof that what flows into it may: by construction
    -- when inferred, decided when annotated.
    storeAt :: Sing (inferred :: SecLevel) -> (forall level. Sing level -> FlowsInto inferred level -> Either ElabError a) -> Either ElabError a
    storeAt inferred k = case annotation of
        Nothing -> k inferred (flowsSelf inferred)
        Just declared -> withSomeSing declared $ \level -> requireFlow "store" inferred level >>= k level

{- | The bulk-memory instructions consume three i32 operands; the typed instruction is
  polymorphic in what lies beneath.
-}
threeAddresses ::
    Text ->
    Sing stackIn ->
    Sing (pc ': pcs) ->
    (forall s ln lsrc ldst. Sing (Join pc (Join ln (Join lsrc ldst))) -> Instr shape ('FrameShape locals ret) labels (pc ': pcs) (pc ': pcs) (('I32 ':~ ln) ': ('I32 ':~ lsrc) ': ('I32 ':~ ldst) ': s) s) ->
    Either ElabError (ElaboratedInstr shape ret locals labels (pc ': pcs) stackIn)
threeAddresses name stackIn pcsIn@(SCons pc _) typed = case stackIn of
    SCons (a :%~ ln) (SCons (b :%~ lsrc) (SCons (c :%~ ldst) rest)) -> do
        Refl <- note (OperandMismatch name I32 (valTypeOf a)) (decideEquality a SI32)
        Refl <- note (OperandMismatch name I32 (valTypeOf b)) (decideEquality b SI32)
        Refl <- note (OperandMismatch name I32 (valTypeOf c)) (decideEquality c SI32)
        Right (Produces (sameLengthAs pcsIn) pcsIn rest (typed (sJoin pc (sJoin ln (sJoin lsrc ldst)))))
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
    forall t r shape ret locals labels pc pcs stackIn.
    Sing (t :: ValType) ->
    Sing (r :: ValType) ->
    Sing (pc ': pcs) ->
    Sing stackIn ->
    (forall s lv lv'. Instr shape ('FrameShape locals ret) labels (pc ': pcs) (pc ': pcs) ((t ':~ lv) ': (t ':~ lv') ': s) ((r ':~ Join pc (Join lv lv')) ': s)) ->
    Either ElabError (ElaboratedInstr shape ret locals labels (pc ': pcs) stackIn)
consumeTwo st sr pcsIn@(SCons pc _) stackIn typed = case stackIn of
    SCons (sa :%~ la) (SCons (sb :%~ lb) rest) -> do
        Refl <- note (OperandMismatch "binary operation" (valTypeOf st) (valTypeOf sa)) (decideEquality sa st)
        Refl <- note (OperandMismatch "binary operation" (valTypeOf st) (valTypeOf sb)) (decideEquality sb st)
        Right (Produces (sameLengthAs pcsIn) pcsIn (SCons (sr :%~ sJoin pc (sJoin la lb)) rest) typed)
    _ -> Left (StackUnderflow "binary operation")

-- | A binary operation whose result has the same type as its (matching) operands.
sameTypeBinary ::
    Sing (t :: ValType) ->
    Sing (pc ': pcs) ->
    Sing stackIn ->
    (forall s lv lv'. Instr shape ('FrameShape locals ret) labels (pc ': pcs) (pc ': pcs) ((t ':~ lv) ': (t ':~ lv') ': s) ((t ':~ Join pc (Join lv lv')) ': s)) ->
    Either ElabError (ElaboratedInstr shape ret locals labels (pc ': pcs) stackIn)
sameTypeBinary st = consumeTwo st st

-- | A unary operation whose result has the same type as its operand.
sameTypeUnary ::
    Sing (t :: ValType) ->
    Sing (pc ': pcs) ->
    Sing stackIn ->
    (forall s lv. Instr shape ('FrameShape locals ret) labels (pc ': pcs) (pc ': pcs) ((t ':~ lv) ': s) ((t ':~ Join pc lv) ': s)) ->
    Either ElabError (ElaboratedInstr shape ret locals labels (pc ': pcs) stackIn)
sameTypeUnary st pcsIn@(SCons pc _) stackIn typed = case stackIn of
    SCons (sa :%~ la) rest -> do
        Refl <- note (OperandMismatch "unary operation" (valTypeOf st) (valTypeOf sa)) (decideEquality sa st)
        Right (Produces (sameLengthAs pcsIn) pcsIn (SCons (st :%~ sJoin pc la) rest) typed)
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

validateDead :: ElabEnv shape ret locals labels -> Sing ((pc :: SecLevel) ': pcs) -> [RawInstr] -> Either ElabError PolyStack
validateDead env pcsIn = go (PolyStack [])
  where
    go s [] = Right s
    go s (i : is) = stepDead env pcsIn s i >>= \s' -> go s' is

{- | A dead tail must still end with the block's result type: each expected type is popped
  (a known entry must match, an unknown one may be anything) and nothing may be left above the
  polymorphic bottom.
-}
checkDeadResult :: PolyStack -> Sing (rs :: [LValType]) -> Either ElabError ()
checkDeadResult final rsS = do
    remaining <- foldM (flip popKnown) final (stackToList rsS)
    case unStack remaining of
        [] -> Right ()
        _ -> Left DeadCodeLeftovers

stepDead :: ElabEnv shape ret locals labels -> Sing ((pc :: SecLevel) ': pcs) -> PolyStack -> RawInstr -> Either ElabError PolyStack
stepDead env pcsIn s instr = case instr of
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
        Just (SomeGlobalRef _ st _) -> Right (pushKnown (unlabelledTypeOf st) s)
    GlobalSet (GlobalIdx g) -> case lookupGlobalRef (globalTypesSing (env.shape)) g of
        Nothing -> Left (IndexOutOfRange Globals g)
        Just (SomeGlobalRef _ st _) -> popKnown (unlabelledTypeOf st) s
    Load t _ -> pushKnown (valTypeOf t) <$> popKnown I32 s
    Store t _ -> popKnown (valTypeOf t) s >>= popKnown I32
    LoadN t _ _ _ -> pushKnown (valTypeOf t) <$> popKnown I32 s
    StoreN t _ _ -> popKnown (valTypeOf t) s >>= popKnown I32
    Annotated _ access -> stepDead env pcsIn s access
    Relabel _ -> Right s
    Declassify _ -> Right s
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
        validateFrame env pcsIn rsT psT rsT body >> afterFrame (stackOrder psT) (stackOrder rsT) s
    Loop (FuncType psT rsT) body ->
        validateFrame env pcsIn psT psT rsT body >> afterFrame (stackOrder psT) (stackOrder rsT) s
    If (FuncType psT rsT) thenB elseB -> do
        s1 <- popKnown I32 s
        validateFrame env pcsIn rsT psT rsT thenB
        validateFrame env pcsIn rsT psT rsT elseB
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
    Sing ((pc :: SecLevel) ': pcs) ->
    [ValType] ->
    [ValType] ->
    [ValType] ->
    [RawInstr] ->
    Either ElabError ()
validateFrame env pcsIn@(SCons pc _) labelT psT rsT body =
    case (reflectStack (stackOrder labelT), reflectStack (stackOrder psT), reflectStack (stackOrder rsT)) of
        (SomeStack labS, SomeStack psS, SomeStack rsS) ->
            elabBodyChecked (pushLabel labS env) (SCons SHigh pcsIn) psS rsS body (\_ -> Right ()) `orElseTry` elabBodyChecked (pushLabel labS env) (SCons pc pcsIn) psS rsS body (\_ -> Right ())
  where
    -- Dead code is never run, so its pc does not matter for security; it is still checked as
    -- code, at the pc it would have had, and at 'High for a loop that would raise its own.
    orElseTry a b = either (const b) Right a

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
    Just (SomeElem sv _) -> k (unlabelledTypeOf sv)
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

{- | The value type of a labelled type, and of a whole labelled stack: what the error reports
and the dead-code checker work with, neither of which looks at security levels.
-}
unlabelledTypeOf :: Sing (t :: LValType) -> ValType
unlabelledTypeOf = unlabelled . fromSing

stackToList :: Sing (s :: [LValType]) -> [ValType]
stackToList = map unlabelled . fromSing

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

  The security levels come from the module's policy ('elaborateModuleWith' and
  "Validation.Policy"); without one everything is public and this accepts exactly the modules
  it accepted before levels existed.
-}
elaborateModule :: RawModule -> Either ElabError SomeModule
elaborateModule = elaborateModuleWith emptyPolicy

{- | 'elaborateModule' under a policy given from outside (a policy file), merged with the one
  the module carries in its @ifc@ custom section; the two may not disagree. Assembly happens
  first, so every level is settled before any function is checked.
-}
elaborateModuleWith :: Policy -> RawModule -> Either ElabError SomeModule
elaborateModuleWith given raw = do
    validateStructure raw
    assembled <- first BadPolicy (sectionPolicy raw >>= mergePolicies given >>= (`assemble` raw))
    let m = assembled.annotated
    case reflectCtx assembled.functionTypes assembled.globalTypes memTypes tableLimits (length m.dataSegments) of
        SomeModuleShape ctxS@(SModuleShape ftsS gsS msS tsS _) -> do
            functions <- elaborateFuncs ctxS (m.types) assembled.declassify ftsS (zip assembled.loadDefaults (map Left m.imports ++ map Right m.functions))
            globals <- elaborateGlobals gsS (m.globals)
            dataSegments <- traverse (elaborateData (memsNonEmpty msS)) (zip [0 ..] m.dataSegments)
            elementSegments <- traverse (elaborateElements ftsS (tablesNonEmpty tsS)) (zip [0 ..] m.elementSegments)
            start <- traverse (resolveStart ftsS) (m.start)
            Right (SomeModule ctxS (Module {functions, globals, dataSegments, elementSegments, exports = m.exports, start}))
  where
    tableLimits = [t.limits | t <- raw.tables]
    memTypes = map (\(RawMemory mt) -> mt) (raw.memories)

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
resolveStart :: Sing (fts :: [LFuncType]) -> FunctionIdx -> Either ElabError (Elem ('FuncType '[] '[]) fts)
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
    Bool ->
    Sing fts ->
    [(SecLevel, Either RawImport RawFunction)] ->
    Either ElabError (FunctionSpace shape fts)
elaborateFuncs _ _ _ SNil [] = Right NoFunctions
elaborateFuncs ctxS types declassify (SCons ft fs) ((loadDefault, entry) : rest) = do
    fs' <- elaborateFuncs ctxS types declassify fs rest
    case entry of
        Left (RawImport moduleName fieldName (ImportFunc _)) -> Right (Imported moduleName fieldName fs')
        Right f -> (`Defined` fs') <$> elaborateFunctionIn ctxS types loadDefault declassify ft f
elaborateFuncs _ _ _ _ _ = Left (Malformed "function/signature count mismatch")

elaborateFunctionIn ::
    SModuleShape shape ->
    [FuncType] ->
    SecLevel ->
    Bool ->
    SFuncTypeOf ft ->
    RawFunction ->
    Either ElabError (Function shape ft)
elaborateFunctionIn ctxS types loadDefault declassify (SFuncType psS rsS) (RawFunction _ declaredT body) =
    case reflectStack declaredT of
        SomeStack declS ->
            let env = ElabEnv ctxS types rsS (sReverseOnto psS declS) (SCons rsS SNil) loadDefault declassify
             in do
                    elaborated <- elabSeq env (SCons SLow SNil) SNil body
                    case elaborated of
                        Reachable _ _ soS bodySeq -> do
                            Refl <- note (ResultMismatch (stackToList rsS) (stackToList soS)) (decideEquality soS rsS)
                            Right (Function psS declS bodySeq)
                        Diverged _ _ final poly -> do
                            checkDeadResult final rsS
                            Right (Function psS declS poly)

elaborateGlobals :: Sing gs -> [RawGlobal] -> Either ElabError (GlobalSpace gs)
elaborateGlobals = go 0
  where
    go :: Word32 -> Sing gs -> [RawGlobal] -> Either ElabError (GlobalSpace gs)
    go _ SNil [] = Right NoGlobals
    go index (SCons (SGlobalType _ (sn :%~ _)) gs) (RawGlobal _ initExpr : rest) = do
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
elaborateElements :: Sing (fts :: [LFuncType]) -> Maybe (NonEmptyTables ts) -> (Int, RawElementSegment) -> Either ElabError (ElementSegment fts)
elaborateElements ftsS tables (index, RawElementSegment offsetExpr functions) = do
    NonEmptyTables <- note (NoTable "elem") tables
    offset <- evalConstInit (InvalidElementSegmentOffset index) SI32 offsetExpr
    refs <- traverse (\(FunctionIdx f) -> note (IndexOutOfRange Functions f) (lookupFuncRef ftsS f)) functions
    Right (ElementSegment offset refs)
