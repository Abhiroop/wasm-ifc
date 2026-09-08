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
    SomeModule (..),
    elaborateModule,
    runModuleFunction,
) where

import Data.Text (Text)
import Data.Text qualified as T
import Data.Type.Equality ((:~:) (Refl))
import Data.Word (Word32)

import Data.List.Singletons ((%++))
import Data.Singletons.Base.TH (SList (SCons, SNil), Sing, fromSing)
import Data.Singletons.Decide (decideEquality)
import Runtime.Interpreter (FuncInst (..), FuncInsts (..), ModuleInst (..), getFunc, runFunction)
import Runtime.MemInst (allocMemory)
import Runtime.Stack (GlobalInsts (..), LocalInsts (..), MemInsts (..), ValueStack (..))
import Syntax.Functions (RawFunction (RawFunction))
import Syntax.Globals (RawGlobal (RawGlobal))
import Syntax.Immediates (HostType)
import Syntax.Indices (FunctionIdx (..), GlobalIdx (..), LabelIdx (..), LocalIdx (..))
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
import Syntax.Memories (RawMemory (RawMemory))
import Syntax.Module
import Syntax.Types
import Validation.Reflect
import Validation.Shape

data ElabError
    = -- | not enough operands on the stack
      StackUnderflow String
    | -- | operand types are wrong
      TypeMismatch String
    | -- | a local/label/function/global index is out of range
      IndexOutOfRange String
    | -- | outside the supported instruction subset
      UnsupportedInstr String
    | -- | a body produced a stack that does not match its type
      ResultMismatch String
    | -- | malformed code after an unconditional transfer
      DeadCodeError String
    | -- | structurally inconsistent module
      Malformed String
    deriving stock (Eq, Show)

-- *** Elaboration environment & results ***

{- | What elaboration knows: the module signature witness, the enclosing function's result
  type and locals, and the result type of each enclosing label.
-}
data ElabEnv (shape :: ModuleShape) (ret :: ResultType) (locals :: [ValType]) (labels :: [ResultType]) = ElabEnv
    { eeShape :: Sing shape
    , eeRet :: Sing ret
    , eeLocals :: Sing locals
    , eeLabels :: Sing labels
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
    universally quantified — exactly the spec's stack-polymorphism for dead code.
    -}
    Diverged :: (forall stackOut. Expr shape ('FrameShape locals ret) labels stackIn stackOut) -> ElaboratedExpr shape ret locals labels stackIn

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

funcTypesSing :: SModuleShape shape -> Sing (ModuleFuncs shape)
funcTypesSing (SModuleShape fts _ _) = fts

globalTypesSing :: SModuleShape shape -> Sing (ModuleGlobals shape)
globalTypesSing (SModuleShape _ gs _) = gs

memShapesSing :: SModuleShape shape -> Sing (ModuleMems shape)
memShapesSing (SModuleShape _ _ ms) = ms

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
                Diverged poly -> Diverged (instr :. poly)
        Transfers transfer -> do
            validateDead env rest
            pure (Diverged (transfer :. INil))

-- *** Single instructions ***

elabInstr ::
    forall shape ret locals labels stackIn.
    ElabEnv shape ret locals labels ->
    Sing stackIn ->
    RawInstr ->
    Either ElabError (ElaboratedInstr shape ret locals labels stackIn)
elabInstr env stackIn instr = case instr of
    {- Constants -}
    Const st literal -> withNum st $ \isNum -> Right (Produces (SCons st stackIn) (IConst isNum literal))
    {- Numeric (consume two of type t, produce one of type t) -}
    Add st -> withNum st $ \isNum -> consumeTwo st st stackIn (IAdd isNum)
    Sub st -> withNum st $ \isNum -> consumeTwo st st stackIn (ISub isNum)
    Mul st -> withNum st $ \isNum -> consumeTwo st st stackIn (IMul isNum)
    Div st sign -> withSignedNum st sign $ \sn -> consumeTwo st st stackIn (IDiv sn)
    Rem st sign -> withInt st $ \isInt -> consumeTwo st st stackIn (IRem isInt sign)
    {- Comparison (consume two of type t, produce one i32). @eqz@ is integer-only. -}
    Eq st -> withNum st $ \isNum -> consumeTwo st SI32 stackIn (IEq isNum)
    Ne st -> withNum st $ \isNum -> consumeTwo st SI32 stackIn (INe isNum)
    Lt st sign -> withSignedNum st sign $ \sn -> consumeTwo st SI32 stackIn (ILt sn)
    Gt st sign -> withSignedNum st sign $ \sn -> consumeTwo st SI32 stackIn (IGt sn)
    Le st sign -> withSignedNum st sign $ \sn -> consumeTwo st SI32 stackIn (ILe sn)
    Ge st sign -> withSignedNum st sign $ \sn -> consumeTwo st SI32 stackIn (IGe sn)
    Eqz st -> withInt st $ \isInt -> case stackIn of
        SCons sa rest -> do
            Refl <- note (TypeMismatch "eqz operand") (decideEquality sa st)
            Right (Produces (SCons SI32 rest) (IEqz isInt))
        _ -> Left (StackUnderflow "eqz")
    {- Stack management -}
    Drop -> case stackIn of
        SCons _ rest -> Right (Produces rest IDrop)
        _ -> Left (StackUnderflow "drop")
    Select -> case stackIn of
        SCons sc (SCons va (SCons vb rest)) -> do
            Refl <- note (TypeMismatch "select condition must be i32") (decideEquality sc SI32)
            Refl <- note (TypeMismatch "select operands have different types") (decideEquality va vb)
            withNum va $ \isNum -> Right (Produces (SCons va rest) (ISelect isNum))
        _ -> Left (StackUnderflow "select")
    {- Locals -}
    LocalGet (LocalIdx i) -> case mkLocalElem (env.eeLocals) i of
        Just (SomeElem sv ix) -> Right (Produces (SCons sv stackIn) (ILocalGet ix))
        Nothing -> Left (IndexOutOfRange ("local.get " ++ show i))
    LocalSet (LocalIdx i) -> case mkLocalElem (env.eeLocals) i of
        Just (SomeElem sv ix) -> case stackIn of
            SCons stop rest -> do
                Refl <- note (TypeMismatch ("local.set " ++ show i)) (decideEquality stop sv)
                Right (Produces rest (ILocalSet ix))
            _ -> Left (StackUnderflow "local.set")
        Nothing -> Left (IndexOutOfRange ("local.set " ++ show i))
    LocalTee (LocalIdx i) -> case mkLocalElem (env.eeLocals) i of
        Just (SomeElem sv ix) -> case stackIn of
            SCons stop _ -> do
                Refl <- note (TypeMismatch ("local.tee " ++ show i)) (decideEquality stop sv)
                Right (Produces stackIn (ILocalTee ix))
            _ -> Left (StackUnderflow "local.tee")
        Nothing -> Left (IndexOutOfRange ("local.tee " ++ show i))
    {- Globals -}
    GlobalGet (GlobalIdx g) -> case lookupGlobalRef (globalTypesSing (env.eeShape)) g of
        Nothing -> Left (IndexOutOfRange ("global.get " ++ show g))
        Just (SomeGlobalRef _ st gix) -> Right (Produces (SCons st stackIn) (IGlobalGet gix))
    GlobalSet (GlobalIdx g) -> case lookupGlobalRef (globalTypesSing (env.eeShape)) g of
        Nothing -> Left (IndexOutOfRange ("global.set " ++ show g))
        Just (SomeGlobalRef smut st gix) -> case smut of
            SImmutable -> Left (TypeMismatch ("global.set " ++ show g ++ ": global is immutable"))
            SMutable -> case stackIn of
                SCons stop rest -> do
                    Refl <- note (TypeMismatch ("global.set " ++ show g)) (decideEquality stop st)
                    Right (Produces rest (IGlobalSet gix))
                _ -> Left (StackUnderflow "global.set")
    {- Memory -}
    Load st memArg -> case memsNonEmpty (memShapesSing (env.eeShape)) of
        Nothing -> Left (TypeMismatch "load: module declares no memory")
        Just NonEmptyMems -> withNum st $ \isNum -> case stackIn of
            SCons sc rest -> do
                Refl <- note (TypeMismatch "load address must be i32") (decideEquality sc SI32)
                checkAlign memArg (numBytes isNum)
                Right (Produces (SCons st rest) (ILoad isNum memArg))
            _ -> Left (StackUnderflow "load")
    Store st memArg -> case memsNonEmpty (memShapesSing (env.eeShape)) of
        Nothing -> Left (TypeMismatch "store: module declares no memory")
        Just NonEmptyMems -> withNum st $ \isNum -> case stackIn of
            SCons sv (SCons sc rest) -> do
                Refl <- note (TypeMismatch "store value type") (decideEquality sv st)
                Refl <- note (TypeMismatch "store address must be i32") (decideEquality sc SI32)
                checkAlign memArg (numBytes isNum)
                Right (Produces rest (IStore isNum memArg))
            _ -> Left (StackUnderflow "store")
    LoadN st width sign memArg -> case memsNonEmpty (memShapesSing (env.eeShape)) of
        Nothing -> Left (TypeMismatch "load: module declares no memory")
        Just NonEmptyMems -> withNarrow st width $ \nw -> case stackIn of
            SCons sc rest -> do
                Refl <- note (TypeMismatch "load address must be i32") (decideEquality sc SI32)
                checkAlign memArg (narrowBytes nw)
                Right (Produces (SCons st rest) (ILoadN nw sign memArg))
            _ -> Left (StackUnderflow "load")
    StoreN st width memArg -> case memsNonEmpty (memShapesSing (env.eeShape)) of
        Nothing -> Left (TypeMismatch "store: module declares no memory")
        Just NonEmptyMems -> withNarrow st width $ \nw -> case stackIn of
            SCons sv (SCons sc rest) -> do
                Refl <- note (TypeMismatch "store value type") (decideEquality sv st)
                Refl <- note (TypeMismatch "store address must be i32") (decideEquality sc SI32)
                checkAlign memArg (narrowBytes nw)
                Right (Produces rest (IStoreN nw memArg))
            _ -> Left (StackUnderflow "store")
    MemorySize -> case memsNonEmpty (memShapesSing (env.eeShape)) of
        Nothing -> Left (TypeMismatch "memory.size: module declares no memory")
        Just NonEmptyMems -> Right (Produces (SCons SI32 stackIn) IMemSize)
    MemoryGrow -> case memsNonEmpty (memShapesSing (env.eeShape)) of
        Nothing -> Left (TypeMismatch "memory.grow: module declares no memory")
        Just NonEmptyMems -> case stackIn of
            SCons sc rest -> do
                Refl <- note (TypeMismatch "memory.grow argument must be i32") (decideEquality sc SI32)
                Right (Produces (SCons SI32 rest) IMemGrow)
            _ -> Left (StackUnderflow "memory.grow")
    {- Calls -}
    Call (FunctionIdx f) -> case lookupFuncRef (funcTypesSing (env.eeShape)) f of
        Nothing -> Left (IndexOutOfRange ("call " ++ show f))
        Just (SomeFuncRef psS rsS fix) -> case matchPrefix psS stackIn of
            Nothing -> Left (TypeMismatch ("call " ++ show f ++ ": arguments not on the stack"))
            Just (SomeSplit sS witness) -> Right (Produces (rsS %++ sS) (ICall witness fix))
    {- Integer bitwise / shift / count (integer types only) -}
    And st -> withInt st $ \isInt -> sameTypeBinary st stackIn (IBitwise isInt BwAnd)
    Or st -> withInt st $ \isInt -> sameTypeBinary st stackIn (IBitwise isInt BwOr)
    Xor st -> withInt st $ \isInt -> sameTypeBinary st stackIn (IBitwise isInt BwXor)
    Shl st -> withInt st $ \isInt -> sameTypeBinary st stackIn (IBitwise isInt BwShl)
    Shr st sign -> withInt st $ \isInt -> sameTypeBinary st stackIn (IBitwise isInt (BwShr sign))
    Rotl st -> withInt st $ \isInt -> sameTypeBinary st stackIn (IBitwise isInt BwRotl)
    Rotr st -> withInt st $ \isInt -> sameTypeBinary st stackIn (IBitwise isInt BwRotr)
    Clz st -> withInt st $ \isInt -> sameTypeUnary st stackIn (ICount isInt OpClz)
    Ctz st -> withInt st $ \isInt -> sameTypeUnary st stackIn (ICount isInt OpCtz)
    Popcnt st -> withInt st $ \isInt -> sameTypeUnary st stackIn (ICount isInt OpPopcnt)
    {- Floating-point unary / binary (floating-point types only) -}
    Abs st -> withFloat st $ \isFloat -> sameTypeUnary st stackIn (IFloatUn isFloat FAbs)
    Neg st -> withFloat st $ \isFloat -> sameTypeUnary st stackIn (IFloatUn isFloat FNeg)
    Sqrt st -> withFloat st $ \isFloat -> sameTypeUnary st stackIn (IFloatUn isFloat FSqrt)
    Ceil st -> withFloat st $ \isFloat -> sameTypeUnary st stackIn (IFloatUn isFloat FCeil)
    Floor st -> withFloat st $ \isFloat -> sameTypeUnary st stackIn (IFloatUn isFloat FFloor)
    FloatTrunc st -> withFloat st $ \isFloat -> sameTypeUnary st stackIn (IFloatUn isFloat FTrunc)
    Nearest st -> withFloat st $ \isFloat -> sameTypeUnary st stackIn (IFloatUn isFloat FNearest)
    Min st -> withFloat st $ \isFloat -> sameTypeBinary st stackIn (IFloatBin isFloat FMin)
    Max st -> withFloat st $ \isFloat -> sameTypeBinary st stackIn (IFloatBin isFloat FMax)
    Copysign st -> withFloat st $ \isFloat -> sameTypeBinary st stackIn (IFloatBin isFloat FCopysign)
    {- Conversions: the opcode's own type indices are the source/result -}
    Convert op ->
        let (nf, nt) = convertEnds op
         in case stackIn of
                SCons sa rest -> do
                    Refl <- note (TypeMismatch "conversion source type") (decideEquality sa (numSing nf))
                    Right (Produces (SCons (numSing nt) rest) (IConvert op))
                _ -> Left (StackUnderflow "conversion")
    {- Inert -}
    Nop -> Right (Produces stackIn INop)
    {- Structured control -}
    Block (FuncType psT rsT) body ->
        case (reflectStack psT, reflectStack rsT) of
            (SomeStack psS, SomeStack rsS) -> case matchPrefix psS stackIn of
                Nothing -> Left (TypeMismatch "block parameters not on the stack")
                Just (SomeSplit sS witness) ->
                    elabBodyChecked (pushLabel rsS env) psS rsS body $ \bodySeq ->
                        Right (Produces (rsS %++ sS) (IBlock witness bodySeq))
    Loop (FuncType psT rsT) body ->
        case (reflectStack psT, reflectStack rsT) of
            (SomeStack psS, SomeStack rsS) -> case matchPrefix psS stackIn of
                Nothing -> Left (TypeMismatch "loop parameters not on the stack")
                Just (SomeSplit sS witness) ->
                    elabBodyChecked (pushLabel psS env) psS rsS body $ \bodySeq ->
                        Right (Produces (rsS %++ sS) (ILoop witness bodySeq))
    If (FuncType psT rsT) thenBody elseBody -> case stackIn of
        SCons sc rest -> do
            Refl <- note (TypeMismatch "if condition must be i32") (decideEquality sc SI32)
            case (reflectStack psT, reflectStack rsT) of
                (SomeStack psS, SomeStack rsS) -> case matchPrefix psS rest of
                    Nothing -> Left (TypeMismatch "if parameters not on the stack")
                    Just (SomeSplit sS witness) ->
                        elabBodyChecked (pushLabel rsS env) psS rsS thenBody $ \thenSeq ->
                            elabBodyChecked (pushLabel rsS env) psS rsS elseBody $ \elseSeq ->
                                Right (Produces (rsS %++ sS) (IIf witness thenSeq elseSeq))
        _ -> Left (StackUnderflow "if")
    {- Branches (unconditional ones diverge) -}
    Br (LabelIdx l) -> case mkLabelElem (env.eeLabels) l of
        Nothing -> Left (IndexOutOfRange ("br " ++ show l))
        Just (SomeLabel rsS labelIx) -> case matchPrefix rsS stackIn of
            Nothing -> Left (TypeMismatch ("br " ++ show l ++ ": operands do not match the label"))
            Just (SomeSplit _ witness) -> Right (Transfers (IBr witness labelIx))
    BrIf (LabelIdx l) -> case stackIn of
        SCons sc rest -> do
            Refl <- note (TypeMismatch "br_if condition must be i32") (decideEquality sc SI32)
            case mkLabelElem (env.eeLabels) l of
                Nothing -> Left (IndexOutOfRange ("br_if " ++ show l))
                Just (SomeLabel rsS labelIx) -> case matchPrefix rsS rest of
                    Nothing -> Left (TypeMismatch ("br_if " ++ show l ++ ": operands do not match the label"))
                    Just (SomeSplit _ witness) -> Right (Produces rest (IBrIf witness labelIx))
        _ -> Left (StackUnderflow "br_if")
    BrTable targets (LabelIdx d) -> case stackIn of
        SCons sc rest -> case decideEquality sc SI32 of
            Nothing -> Left (TypeMismatch "br_table index must be i32")
            Just Refl -> case mkLabelElem (env.eeLabels) d of
                Nothing -> Left (IndexOutOfRange ("br_table default " ++ show d))
                Just (SomeLabel rsS defIx) -> case mapM (resolveTarget env rsS) targets of
                    Left err -> Left err
                    Right targetIxs -> case matchPrefix rsS rest of
                        Nothing -> Left (TypeMismatch "br_table operands do not match the labels")
                        Just (SomeSplit _ witness) -> Right (Transfers (IBrTable witness targetIxs defIx))
        _ -> Left (StackUnderflow "br_table")
    Return -> case matchPrefix (env.eeRet) stackIn of
        Nothing -> Left (TypeMismatch "return: operands do not match the result type")
        Just (SomeSplit _ witness) -> Right (Transfers (IReturn witness))
    Unreachable -> Right (Transfers IUnreachable)

-- | Push a label's result type onto the elaboration environment's label context.
pushLabel :: Sing rs -> ElabEnv shape ret locals labels -> ElabEnv shape ret locals (rs ': labels)
pushLabel rsS env = env {eeLabels = SCons rsS (env.eeLabels)}

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
            Refl <- note (ResultMismatch "body result does not match its block type") (decideEquality soS rsS)
            k seq'
        Diverged poly -> k poly

-- | Resolve one @br_table@ target, checking it carries the same result type as the rest.
resolveTarget :: ElabEnv shape ret locals labels -> Sing rs -> LabelIdx -> Either ElabError (Elem rs labels)
resolveTarget env rsS (LabelIdx t) = case mkLabelElem (env.eeLabels) t of
    Nothing -> Left (IndexOutOfRange ("br_table target " ++ show t))
    Just (SomeLabel rsS' targetIx) -> case decideEquality rsS' rsS of
        Just Refl -> Right targetIx
        Nothing -> Left (TypeMismatch "br_table targets have different types")

{- | Refine an operation's operand type to numeric (resp. integer, floating-point) evidence,
  failing elaboration if it is of the wrong kind (e.g. @funcref.add@, @f32.and@ or
  @i32.sqrt@). This is what lets the typed instruction carry the exact constraint the spec
  demands, and lets the interpreter dispatch it totally with no wrong-kind fall-through.
-}
withNum :: Sing (t :: ValType) -> (IsNum t -> Either ElabError a) -> Either ElabError a
withNum st k = maybe (Left (TypeMismatch "operation requires a numeric type")) k (numType st)

withInt :: Sing (t :: ValType) -> (IsInt t -> Either ElabError a) -> Either ElabError a
withInt st k = maybe (Left (TypeMismatch "operation requires an integer type")) k (intType st)

withFloat :: Sing (t :: ValType) -> (IsFloat t -> Either ElabError a) -> Either ElabError a
withFloat st k = maybe (Left (TypeMismatch "operation requires a floating-point type")) k (floatType st)

{- | Refine to a 'SignedNum' for @div@ and the ordered comparisons: the signedness is kept for
  integers and dropped for floats (a signed float comparison/division is thus unrepresentable).
-}
withSignedNum :: Sing (t :: ValType) -> Signedness -> (SignedNum t -> Either ElabError a) -> Either ElabError a
withSignedNum st sign k = maybe (Left (TypeMismatch "operation requires a numeric type")) k (signedNum st sign)

{- | Refine an integer type and a byte width to a 'NarrowWidth', rejecting widths that are not
  a valid narrow access for the type (so @i32.load8@ is fine but a 100-byte narrow load is not).
-}
withNarrow :: Sing (t :: ValType) -> Int -> (NarrowWidth t -> Either ElabError a) -> Either ElabError a
withNarrow st width k = maybe (Left (TypeMismatch "invalid narrow memory access width")) k (narrowWidth st width)

{- | The spec bounds a memory access's alignment by its width: @2^align <= accessBytes@. The
  binary format stores @align@ as the log2 exponent, so a valid exponent is at most 3 (for an
  8-byte access); anything larger is rejected without computing an overflowing @2^align@.
-}
checkAlign :: MemArg -> Int -> Either ElabError ()
checkAlign memArg accessBytes
    | align <= 3 && (2 ^ align :: Int) <= accessBytes = Right ()
    | otherwise = Left (TypeMismatch "alignment exceeds the access width")
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
        Refl <- note (TypeMismatch "binary op operand 1") (decideEquality sa st)
        Refl <- note (TypeMismatch "binary op operand 2") (decideEquality sb st)
        Right (Produces (SCons sr rest) typed)
    _ -> Left (StackUnderflow "binary numeric op")

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
        Refl <- note (TypeMismatch "unary op operand") (decideEquality sa st)
        Right (Produces (SCons st rest) typed)
    _ -> Left (StackUnderflow "unary numeric op")

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
        | otherwise -> Left (DeadCodeError msg)
      where
        msg = "unreachable code expected " ++ show t ++ ", found " ++ show v

validateDead :: ElabEnv shape ret locals labels -> [RawInstr] -> Either ElabError ()
validateDead env = go (PolyStack [])
  where
    go _ [] = Right ()
    go s (i : is) = stepDead env s i >>= \s' -> go s' is

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
        Right (PolyStack (orElse a b : unStack s3))
    LocalGet (LocalIdx i) -> withLocal env i (\v -> Right (pushKnown v s))
    LocalSet (LocalIdx i) -> withLocal env i (\v -> popKnown v s)
    LocalTee (LocalIdx i) -> withLocal env i (\v -> pushKnown v <$> popKnown v s)
    GlobalGet (GlobalIdx g) -> case lookupGlobalRef (globalTypesSing (env.eeShape)) g of
        Nothing -> Left (IndexOutOfRange ("global.get " ++ show g ++ " (unreachable)"))
        Just (SomeGlobalRef _ st _) -> Right (pushKnown (valTypeOf st) s)
    GlobalSet (GlobalIdx g) -> case lookupGlobalRef (globalTypesSing (env.eeShape)) g of
        Nothing -> Left (IndexOutOfRange ("global.set " ++ show g ++ " (unreachable)"))
        Just (SomeGlobalRef _ st _) -> popKnown (valTypeOf st) s
    Load t _ -> pushKnown (valTypeOf t) <$> popKnown I32 s
    Store t _ -> popKnown (valTypeOf t) s >>= popKnown I32
    LoadN t _ _ _ -> pushKnown (valTypeOf t) <$> popKnown I32 s
    StoreN t _ _ -> popKnown (valTypeOf t) s >>= popKnown I32
    MemorySize -> Right (pushKnown I32 s)
    MemoryGrow -> pushKnown I32 <$> popKnown I32 s
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
    Call (FunctionIdx f) -> case lookupFuncRef (funcTypesSing (env.eeShape)) f of
        Nothing -> Left (IndexOutOfRange ("call " ++ show f ++ " (unreachable)"))
        Just (SomeFuncRef psS rsS _) -> afterFrame (stackToList psS) (stackToList rsS) s
    Nop -> Right s
    Block (FuncType psT rsT) body -> validateFrame env rsT psT rsT body >> afterFrame psT rsT s
    Loop (FuncType psT rsT) body -> validateFrame env psT psT rsT body >> afterFrame psT rsT s
    If (FuncType psT rsT) thenB elseB -> do
        s1 <- popKnown I32 s
        validateFrame env rsT psT rsT thenB
        validateFrame env rsT psT rsT elseB
        afterFrame psT rsT s1
    Br (LabelIdx l) -> checkLabel env l >> Right s
    BrIf (LabelIdx l) -> popKnown I32 s >>= \s' -> checkLabel env l >> Right s'
    BrTable targets (LabelIdx d) -> do
        s' <- popKnown I32 s
        mapM_ (\(LabelIdx t) -> checkLabel env t) targets
        checkLabel env d
        Right s'
    Return -> Right s
    Unreachable -> Right s
  where
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

-- | Validate a nested block/loop/if body — a fresh, reachable frame — discarding its AST.
validateFrame ::
    ElabEnv shape ret locals labels ->
    [ValType] ->
    [ValType] ->
    [ValType] ->
    [RawInstr] ->
    Either ElabError ()
validateFrame env labelT psT rsT body =
    case (reflectStack labelT, reflectStack psT, reflectStack rsT) of
        (SomeStack labS, SomeStack psS, SomeStack rsS) ->
            elabBodyChecked (pushLabel labS env) psS rsS body (\_ -> Right ())

afterFrame :: [ValType] -> [ValType] -> PolyStack -> Either ElabError PolyStack
afterFrame psT rsT s = Right (pushResults rsT (popN (length psT) s))
  where
    popN 0 t = t
    popN n t = popN (n - 1) (snd (popAny t))
    pushResults vs t = foldr pushKnown t (reverse vs)

withLocal :: ElabEnv shape ret locals labels -> Word32 -> (ValType -> Either ElabError a) -> Either ElabError a
withLocal env i k = case mkLocalElem (env.eeLocals) i of
    Just (SomeElem sv _) -> k (valTypeOf sv)
    Nothing -> Left (IndexOutOfRange ("local " ++ show i ++ " (unreachable code)"))

checkLabel :: ElabEnv shape ret locals labels -> Word32 -> Either ElabError ()
checkLabel env l = case mkLabelElem (env.eeLabels) l of
    Just _ -> Right ()
    Nothing -> Left (IndexOutOfRange ("label " ++ show l ++ " (unreachable code)"))

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

{- | A fully elaborated, well-typed module: its signature witness, its typed instances, and
  its exports (for resolving entry points).
-}
data SomeModule where
    SomeModule :: SModuleShape shape -> ModuleInst shape -> [Export] -> SomeModule

{- | Type-check an entire decoded module: build its signature, elaborate every function
  against it, and assemble the typed functions, initial globals and memories.
-}
elaborateModule :: RawModule -> Either ElabError SomeModule
elaborateModule m =
    case reflectCtx funcSigs globalTypes memTypes of
        SomeModuleShape ctxS@(SModuleShape ftsS gsS msS) -> do
            funcs <- elaborateFuncs ctxS ftsS (m.moduleFuncs)
            globals <- buildGlobals gsS (m.moduleGlobals)
            mems <- buildMems msS (m.moduleMemories)
            Right (SomeModule ctxS (ModuleInst funcs globals mems) (m.moduleExports))
  where
    funcSigs = map (\(RawFunction sig _ _) -> sig) (m.moduleFuncs)
    globalTypes = map (\(RawGlobal gt _) -> gt) (m.moduleGlobals)
    memTypes = map (\(RawMemory mt) -> mt) (m.moduleMemories)

elaborateFuncs :: SModuleShape shape -> Sing fts -> [RawFunction] -> Either ElabError (FuncInsts shape fts)
elaborateFuncs _ SNil [] = Right FsNil
elaborateFuncs ctxS (SCons ft fs) (rf : rfs) = do
    f <- elaborateFunctionIn ctxS ft rf
    fs' <- elaborateFuncs ctxS fs rfs
    Right (FsCons f fs')
elaborateFuncs _ _ _ = Left (Malformed "function/signature count mismatch")

elaborateFunctionIn ::
    SModuleShape shape ->
    SFuncType ft ->
    RawFunction ->
    Either ElabError (FuncInst shape ft)
elaborateFunctionIn ctxS (SFuncType psS rsS) (RawFunction _ declaredT body) =
    case reflectStack declaredT of
        SomeStack declS ->
            let env = ElabEnv ctxS rsS (psS %++ declS) (SCons rsS SNil)
                defaults = defaultLocals declS
             in do
                    elaborated <- elabSeq env SNil body
                    case elaborated of
                        Reachable soS bodySeq -> do
                            Refl <-
                                note
                                    (ResultMismatch "function body does not match its result type")
                                    (decideEquality soS rsS)
                            Right (FuncInst defaults bodySeq)
                        Diverged poly -> Right (FuncInst defaults poly)

buildGlobals :: Sing gs -> [RawGlobal] -> Either ElabError (GlobalInsts gs)
buildGlobals SNil [] = Right GNil
buildGlobals (SCons (SGlobalType _ sn) gs) (RawGlobal _ initExpr : rest) = do
    value <- evalConstInit sn initExpr
    rest' <- buildGlobals gs rest
    Right (GCons value rest')
buildGlobals _ _ = Left (Malformed "global/type count mismatch")

evalConstInit :: Sing (n :: ValType) -> [RawInstr] -> Either ElabError (HostType n)
evalConstInit sn [Const st literal] = case decideEquality st sn of
    Just Refl -> Right literal
    Nothing -> Left (TypeMismatch "global initializer type mismatch")
evalConstInit _ _ = Left (UnsupportedInstr "non-constant global initializer")

{- | Build the runtime memories matching the module's declared memory shapes, each allocated
  at its minimum page count.
-}
buildMems :: Sing ms -> [RawMemory] -> Either ElabError (MemInsts ms)
buildMems SNil [] = Right MNil
buildMems (SCons _ rest) (RawMemory (MemType _ (Limits minPages _)) : rms) =
    MCons (allocMemory minPages) <$> buildMems rest rms
buildMems _ _ = Left (Malformed "memory/type count mismatch")

-- | Zero-initialise a locals frame of the given shape.
defaultLocals :: Sing ds -> LocalInsts ds
defaultLocals SNil = LNil
defaultLocals (SCons sn ds) = zeroOf sn :& defaultLocals ds

zeroOf :: Sing (n :: ValType) -> HostType n
zeroOf SI32 = 0
zeroOf SI64 = 0
zeroOf SF32 = 0
zeroOf SF64 = 0

-- *** Running an exported function ***

{- | Resolve an export, build a typed argument stack from integer literals, run the
  function on the module, and render the results.
-}
runModuleFunction :: SomeModule -> Text -> [Integer] -> Either String [String]
runModuleFunction (SomeModule ctxS typedModule exports) name args =
    case exportedFuncIndex name exports of
        Nothing -> Left ("no exported function named " ++ T.unpack name)
        Just (FunctionIdx idx) -> case lookupFuncRef (funcTypesSing ctxS) idx of
            Nothing -> Left "exported function index out of range"
            Just (SomeFuncRef paramsS resultsS funcIx) -> do
                argStack <- buildArgs paramsS args
                case runFunction typedModule (getFunc funcIx (typedModule.miFuncs)) argStack of
                    Left aTrap -> Left ("trap: " ++ show aTrap)
                    Right vals -> Right (renderResults resultsS vals)

exportedFuncIndex :: Text -> [Export] -> Maybe FunctionIdx
exportedFuncIndex name exports =
    case [idx | Export n (ExportFunc idx) <- exports, n == name] of
        (idx : _) -> Just idx
        [] -> Nothing

buildArgs :: Sing ps -> [Integer] -> Either String (ValueStack ps)
buildArgs SNil [] = Right VNil
buildArgs SNil _ = Left "too many arguments"
buildArgs (SCons _ _) [] = Left "too few arguments"
buildArgs (SCons sn r) (a : as) = (fromIntegerOf sn a :#) <$> buildArgs r as

renderResults :: Sing rs -> ValueStack rs -> [String]
renderResults SNil VNil = []
renderResults (SCons sn r) (v :# vs) = showOf sn v : renderResults r vs

fromIntegerOf :: Sing (n :: ValType) -> Integer -> HostType n
fromIntegerOf SI32 = fromInteger
fromIntegerOf SI64 = fromInteger
fromIntegerOf SF32 = fromInteger
fromIntegerOf SF64 = fromInteger

showOf :: Sing (n :: ValType) -> HostType n -> String
showOf SI32 = show
showOf SI64 = show
showOf SF32 = show
showOf SF64 = show
