{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

-- | Elaboration: type-checking a decoded module and, where it succeeds, building the
--   corresponding intrinsically-typed AST with its indices recovered — the bridge from the
--   untyped (decoded) representation to the typed interpreter.
--
--   Elaboration runs against a runtime witness of the module signature ('ModuleShapeS'), so it
--   covers the whole module: @call@ between functions, globals and memory are all checked.
--   Dead code after an unconditional transfer is validated under the spec's polymorphic
--   stack ('validateDead'); nested block/loop/if bodies are fresh, reachable frames.
module Validation.Elaborate
    ( ElabError (..)
    , SomeModule (..)
    , elaborateModule
    , runModuleFunction
    ) where

import Data.Text          (Text)
import qualified Data.Text as T
import Data.Type.Equality ((:~:) (Refl))
import Data.Word          (Word32)

import Runtime.MemInst      (allocMemory)
import Runtime.Values     (RuntimeHostType)
import Syntax.Functions   (RawFunction (RawFunction))
import Syntax.Globals     (RawGlobal (RawGlobal))
import Syntax.Indices     (FunctionIdx (..), GlobalIdx (..), LabelIdx (..), LocalIdx (..))
import Syntax.Instructions (ConvertOp (..), RawInstr (..))
import Syntax.Memories    (RawMemory (RawMemory))
import Syntax.Module
import Syntax.Types
import Validation.Shape      (ModuleFuncs, ModuleGlobals, ModuleMems, Elem)
import Syntax.Instructions (BitwiseOp (..), CountOp (..), FloatBinOp (..), FloatUnOp (..),
                           Instr (..), Expr (..))
import Runtime.Interpreter  (FuncInst (..), FuncInsts (..), ModuleInst (..), getFunc, runFunction)
import Validation.Reflect
import Runtime.Stack        (GlobalInsts (..), LocalInsts (..), MemInsts (..), ValueStack (..))

data ElabError
    = StackUnderflow String    -- ^ not enough operands on the stack
    | TypeMismatch String      -- ^ operand types are wrong
    | IndexOutOfRange String   -- ^ a local/label/function/global index is out of range
    | UnsupportedInstr String  -- ^ outside the supported instruction subset
    | ResultMismatch String    -- ^ a body produced a stack that does not match its type
    | DeadCodeError String     -- ^ malformed code after an unconditional transfer
    | Malformed String         -- ^ structurally inconsistent module
    deriving (Eq, Show)

{- *** Elaboration environment & results *** -}

-- | What elaboration knows: the module signature witness, the enclosing function's result
--   type and locals, and the result type of each enclosing label.
data ElabEnv shape ret locals labels = ElabEnv
    { eeShape    :: ModuleShapeS shape
    , eeRet    :: StackS ret
    , eeLocals :: StackS locals
    , eeLabels :: LabelS labels
    }

-- | The result of elaborating a sequence from input stack @si@: either it falls through
--   with a concrete output stack, or it ends in an unconditional transfer and its output
--   is universally quantified (the dead tail is validated but not represented).
data Elab shape ret locals labels si where
    Reachable :: StackS so -> Expr shape ret locals labels si so -> Elab shape ret locals labels si
    Diverged  :: (forall so. Expr shape ret locals labels si so) -> Elab shape ret locals labels si

-- | The result of elaborating one instruction.
data Step shape ret locals labels si where
    StepTo   :: StackS so -> Instr shape ret locals labels si so -> Step shape ret locals labels si
    StepAway :: (forall so. Instr shape ret locals labels si so) -> Step shape ret locals labels si

note :: ElabError -> Maybe a -> Either ElabError a
note e = maybe (Left e) Right

shapeFuncsS :: ModuleShapeS shape -> FuncTypesS (ModuleFuncs shape)
shapeFuncsS (ModuleShapeS fts _ _) = fts

shapeGlobalsS :: ModuleShapeS shape -> GlobalsS (ModuleGlobals shape)
shapeGlobalsS (ModuleShapeS _ gs _) = gs

shapeMemsS :: ModuleShapeS shape -> MemsS (ModuleMems shape)
shapeMemsS (ModuleShapeS _ _ ms) = ms

{- *** Sequences *** -}

elabSeq :: ElabEnv shape ret locals labels -> StackS si -> [RawInstr]
        -> Either ElabError (Elab shape ret locals labels si)
elabSeq _   si []           = Right (Reachable si INil)
elabSeq env si (raw : rest) = do
    step <- elabInstr env si raw
    case step of
        StepTo so instr -> do
            rest' <- elabSeq env so rest
            pure $ case rest' of
                Reachable so' seq' -> Reachable so' (instr :. seq')
                Diverged poly      -> Diverged (instr :. poly)
        StepAway transfer -> do
            validateDead env rest
            pure (Diverged (transfer :. INil))

{- *** Single instructions *** -}

elabInstr :: forall shape ret locals labels si.
             ElabEnv shape ret locals labels -> StackS si -> RawInstr
          -> Either ElabError (Step shape ret locals labels si)
elabInstr env si instr = case instr of
    {- Constants -}
    Const st literal -> Right (StepTo (SSCons (SNum st) si) (IConst st literal))

    {- Numeric (consume two of type t, produce one of type t) -}
    Add st     -> consumeTwo st (SNum st) si (IAdd st)
    Sub st     -> consumeTwo st (SNum st) si (ISub st)
    Mul st     -> consumeTwo st (SNum st) si (IMul st)
    Div st sign -> consumeTwo st (SNum st) si (IDiv st sign)
    Rem st sign -> withInt st $ \isInt -> consumeTwo st (SNum st) si (IRem isInt sign)

    {- Comparison (consume two of type t, produce one i32) -}
    Eq st      -> consumeTwo st (SNum SI32) si (IEq st)
    Ne st      -> consumeTwo st (SNum SI32) si (INe st)
    Lt st sign  -> consumeTwo st (SNum SI32) si (ILt st sign)
    Gt st sign  -> consumeTwo st (SNum SI32) si (IGt st sign)
    Le st sign  -> consumeTwo st (SNum SI32) si (ILe st sign)
    Ge st sign  -> consumeTwo st (SNum SI32) si (IGe st sign)
    Eqz st     -> case si of
        SSCons (SNum sa) rest -> do
            Refl <- note (TypeMismatch "eqz operand") (decideNumType sa st)
            Right (StepTo (SSCons (SNum SI32) rest) (IEqz st))
        _ -> Left (StackUnderflow "eqz")

    {- Stack management -}
    Drop -> case si of
        SSCons _ rest -> Right (StepTo rest IDrop)
        _             -> Left (StackUnderflow "drop")
    Select -> case si of
        SSCons (SNum sc) (SSCons va (SSCons vb rest)) -> do
            Refl <- note (TypeMismatch "select condition must be i32") (decideNumType sc SI32)
            Refl <- note (TypeMismatch "select operands have different types") (decideValType va vb)
            Right (StepTo (SSCons va rest) ISelect)
        _ -> Left (StackUnderflow "select")

    {- Locals -}
    LocalGet (LocalIdx i) -> case mkLocalElem (eeLocals env) i of
        Just (SomeElem sv ix) -> Right (StepTo (SSCons sv si) (ILocalGet ix))
        Nothing               -> Left (IndexOutOfRange ("local.get " ++ show i))
    LocalSet (LocalIdx i) -> case mkLocalElem (eeLocals env) i of
        Just (SomeElem sv ix) -> case si of
            SSCons stop rest -> do
                Refl <- note (TypeMismatch ("local.set " ++ show i)) (decideValType stop sv)
                Right (StepTo rest (ILocalSet ix))
            _ -> Left (StackUnderflow "local.set")
        Nothing -> Left (IndexOutOfRange ("local.set " ++ show i))
    LocalTee (LocalIdx i) -> case mkLocalElem (eeLocals env) i of
        Just (SomeElem sv ix) -> case si of
            SSCons stop _ -> do
                Refl <- note (TypeMismatch ("local.tee " ++ show i)) (decideValType stop sv)
                Right (StepTo si (ILocalTee ix))
            _ -> Left (StackUnderflow "local.tee")
        Nothing -> Left (IndexOutOfRange ("local.tee " ++ show i))

    {- Globals -}
    GlobalGet (GlobalIdx g) -> case lookupGlobalRef (shapeGlobalsS (eeShape env)) g of
        Nothing -> Left (IndexOutOfRange ("global.get " ++ show g))
        Just (SomeGlobalRef _ st gix) -> Right (StepTo (SSCons st si) (IGlobalGet gix))
    GlobalSet (GlobalIdx g) -> case lookupGlobalRef (shapeGlobalsS (eeShape env)) g of
        Nothing -> Left (IndexOutOfRange ("global.set " ++ show g))
        Just (SomeGlobalRef smut st gix) -> case smut of
            SImmutable -> Left (TypeMismatch ("global.set " ++ show g ++ ": global is immutable"))
            SMutable -> case si of
                SSCons stop rest -> do
                    Refl <- note (TypeMismatch ("global.set " ++ show g)) (decideValType stop st)
                    Right (StepTo rest (IGlobalSet gix))
                _ -> Left (StackUnderflow "global.set")

    {- Memory -}
    Load st memArg -> case memsNonEmpty (shapeMemsS (eeShape env)) of
        Nothing -> Left (TypeMismatch "load: module declares no memory")
        Just NonEmptyMems -> case si of
            SSCons (SNum sc) rest -> do
                Refl <- note (TypeMismatch "load address must be i32") (decideNumType sc SI32)
                Right (StepTo (SSCons (SNum st) rest) (ILoad st memArg))
            _ -> Left (StackUnderflow "load")
    Store st memArg -> case memsNonEmpty (shapeMemsS (eeShape env)) of
        Nothing -> Left (TypeMismatch "store: module declares no memory")
        Just NonEmptyMems -> case si of
            SSCons (SNum sv) (SSCons (SNum sc) rest) -> do
                Refl <- note (TypeMismatch "store value type") (decideNumType sv st)
                Refl <- note (TypeMismatch "store address must be i32") (decideNumType sc SI32)
                Right (StepTo rest (IStore st memArg))
            _ -> Left (StackUnderflow "store")

    LoadN st width sign memArg -> case memsNonEmpty (shapeMemsS (eeShape env)) of
        Nothing -> Left (TypeMismatch "load: module declares no memory")
        Just NonEmptyMems -> withInt st $ \isInt -> case si of
            SSCons (SNum sc) rest -> do
                Refl <- note (TypeMismatch "load address must be i32") (decideNumType sc SI32)
                Right (StepTo (SSCons (SNum st) rest) (ILoadN isInt width sign memArg))
            _ -> Left (StackUnderflow "load")
    StoreN st width memArg -> case memsNonEmpty (shapeMemsS (eeShape env)) of
        Nothing -> Left (TypeMismatch "store: module declares no memory")
        Just NonEmptyMems -> withInt st $ \isInt -> case si of
            SSCons (SNum sv) (SSCons (SNum sc) rest) -> do
                Refl <- note (TypeMismatch "store value type") (decideNumType sv st)
                Refl <- note (TypeMismatch "store address must be i32") (decideNumType sc SI32)
                Right (StepTo rest (IStoreN isInt width memArg))
            _ -> Left (StackUnderflow "store")
    MemorySize -> case memsNonEmpty (shapeMemsS (eeShape env)) of
        Nothing            -> Left (TypeMismatch "memory.size: module declares no memory")
        Just NonEmptyMems  -> Right (StepTo (SSCons (SNum SI32) si) IMemSize)
    MemoryGrow -> case memsNonEmpty (shapeMemsS (eeShape env)) of
        Nothing           -> Left (TypeMismatch "memory.grow: module declares no memory")
        Just NonEmptyMems -> case si of
            SSCons (SNum sc) rest -> do
                Refl <- note (TypeMismatch "memory.grow argument must be i32") (decideNumType sc SI32)
                Right (StepTo (SSCons (SNum SI32) rest) IMemGrow)
            _ -> Left (StackUnderflow "memory.grow")

    {- Calls -}
    Call (FunctionIdx f) -> case lookupFuncRef (shapeFuncsS (eeShape env)) f of
        Nothing -> Left (IndexOutOfRange ("call " ++ show f))
        Just (SomeFuncRef psS rsS fix) -> case matchPrefix psS si of
            Nothing -> Left (TypeMismatch ("call " ++ show f ++ ": arguments not on the stack"))
            Just (SomeSplit sS witness) -> Right (StepTo (sAppendS rsS sS) (ICall witness fix))

    {- Integer bitwise / shift / count (integer types only) -}
    And st     -> withInt st $ \isInt -> sameTypeBinary st si (IBitwise isInt BwAnd)
    Or  st     -> withInt st $ \isInt -> sameTypeBinary st si (IBitwise isInt BwOr)
    Xor st     -> withInt st $ \isInt -> sameTypeBinary st si (IBitwise isInt BwXor)
    Shl st     -> withInt st $ \isInt -> sameTypeBinary st si (IBitwise isInt BwShl)
    Shr st sign -> withInt st $ \isInt -> sameTypeBinary st si (IBitwise isInt (BwShr sign))
    Rotl st    -> withInt st $ \isInt -> sameTypeBinary st si (IBitwise isInt BwRotl)
    Rotr st    -> withInt st $ \isInt -> sameTypeBinary st si (IBitwise isInt BwRotr)
    Clz st     -> withInt st $ \isInt -> sameTypeUnary st si (ICount isInt OpClz)
    Ctz st     -> withInt st $ \isInt -> sameTypeUnary st si (ICount isInt OpCtz)
    Popcnt st  -> withInt st $ \isInt -> sameTypeUnary st si (ICount isInt OpPopcnt)

    {- Floating-point unary / binary (floating-point types only) -}
    Abs st        -> withFloat st $ \isFloat -> sameTypeUnary  st si (IFloatUn isFloat FAbs)
    Neg st        -> withFloat st $ \isFloat -> sameTypeUnary  st si (IFloatUn isFloat FNeg)
    Sqrt st       -> withFloat st $ \isFloat -> sameTypeUnary  st si (IFloatUn isFloat FSqrt)
    Ceil st       -> withFloat st $ \isFloat -> sameTypeUnary  st si (IFloatUn isFloat FCeil)
    Floor st      -> withFloat st $ \isFloat -> sameTypeUnary  st si (IFloatUn isFloat FFloor)
    FloatTrunc st -> withFloat st $ \isFloat -> sameTypeUnary  st si (IFloatUn isFloat FTrunc)
    Nearest st    -> withFloat st $ \isFloat -> sameTypeUnary  st si (IFloatUn isFloat FNearest)
    Min st        -> withFloat st $ \isFloat -> sameTypeBinary st si (IFloatBin isFloat FMin)
    Max st        -> withFloat st $ \isFloat -> sameTypeBinary st si (IFloatBin isFloat FMax)
    Copysign st   -> withFloat st $ \isFloat -> sameTypeBinary st si (IFloatBin isFloat FCopysign)

    {- Conversions: derive the source/result singletons from the opcode -}
    Convert op ->
        let (Num fromN, Num toN) = convertSig op
        in case (reflectNum fromN, reflectNum toN) of
            (SomeNum sFrom, SomeNum sTo) -> case si of
                SSCons (SNum sa) rest -> do
                    Refl <- note (TypeMismatch "conversion source type") (decideNumType sa sFrom)
                    Right (StepTo (SSCons (SNum sTo) rest) (IConvert sFrom sTo op))
                _ -> Left (StackUnderflow "conversion")

    {- Inert -}
    Nop -> Right (StepTo si INop)

    {- Structured control -}
    Block (FuncType psT rsT) body ->
        case (reflectStack psT, reflectStack rsT) of
            (SomeStack psS, SomeStack rsS) -> case matchPrefix psS si of
                Nothing -> Left (TypeMismatch "block parameters not on the stack")
                Just (SomeSplit sS witness) ->
                    elabBodyChecked (pushLabel rsS env) psS rsS body $ \bodySeq ->
                        Right (StepTo (sAppendS rsS sS) (IBlock witness bodySeq))
    Loop (FuncType psT rsT) body ->
        case (reflectStack psT, reflectStack rsT) of
            (SomeStack psS, SomeStack rsS) -> case matchPrefix psS si of
                Nothing -> Left (TypeMismatch "loop parameters not on the stack")
                Just (SomeSplit sS witness) ->
                    elabBodyChecked (pushLabel psS env) psS rsS body $ \bodySeq ->
                        Right (StepTo (sAppendS rsS sS) (ILoop witness bodySeq))
    If (FuncType psT rsT) thenBody elseBody -> case si of
        SSCons (SNum sc) rest -> do
            Refl <- note (TypeMismatch "if condition must be i32") (decideNumType sc SI32)
            case (reflectStack psT, reflectStack rsT) of
                (SomeStack psS, SomeStack rsS) -> case matchPrefix psS rest of
                    Nothing -> Left (TypeMismatch "if parameters not on the stack")
                    Just (SomeSplit sS witness) ->
                        elabBodyChecked (pushLabel rsS env) psS rsS thenBody $ \thenSeq ->
                        elabBodyChecked (pushLabel rsS env) psS rsS elseBody $ \elseSeq ->
                            Right (StepTo (sAppendS rsS sS) (IIf witness thenSeq elseSeq))
        _ -> Left (StackUnderflow "if")

    {- Branches (unconditional ones diverge) -}
    Br (LabelIdx l) -> case mkLabelElem (eeLabels env) l of
        Nothing -> Left (IndexOutOfRange ("br " ++ show l))
        Just (SomeLabel rsS labelIx) -> case matchPrefix rsS si of
            Nothing -> Left (TypeMismatch ("br " ++ show l ++ ": operands do not match the label"))
            Just (SomeSplit _ witness) -> Right (StepAway (IBr witness labelIx))
    BrIf (LabelIdx l) -> case si of
        SSCons (SNum sc) rest -> do
            Refl <- note (TypeMismatch "br_if condition must be i32") (decideNumType sc SI32)
            case mkLabelElem (eeLabels env) l of
                Nothing -> Left (IndexOutOfRange ("br_if " ++ show l))
                Just (SomeLabel rsS labelIx) -> case matchPrefix rsS rest of
                    Nothing -> Left (TypeMismatch ("br_if " ++ show l ++ ": operands do not match the label"))
                    Just (SomeSplit _ witness) -> Right (StepTo rest (IBrIf witness labelIx))
        _ -> Left (StackUnderflow "br_if")
    BrTable targets (LabelIdx d) -> case si of
        SSCons (SNum sc) rest -> case decideNumType sc SI32 of
            Nothing   -> Left (TypeMismatch "br_table index must be i32")
            Just Refl -> case mkLabelElem (eeLabels env) d of
                Nothing -> Left (IndexOutOfRange ("br_table default " ++ show d))
                Just (SomeLabel rsS defIx) -> case mapM (resolveTarget env rsS) targets of
                    Left err        -> Left err
                    Right targetIxs -> case matchPrefix rsS rest of
                        Nothing -> Left (TypeMismatch "br_table operands do not match the labels")
                        Just (SomeSplit _ witness) -> Right (StepAway (IBrTable witness targetIxs defIx))
        _ -> Left (StackUnderflow "br_table")
    Return -> case matchPrefix (eeRet env) si of
        Nothing -> Left (TypeMismatch "return: operands do not match the result type")
        Just (SomeSplit _ witness) -> Right (StepAway (IReturn witness))
    Unreachable -> Right (StepAway IUnreachable)

-- | Push a label's result type onto the elaboration environment's label context.
pushLabel :: StackS rs -> ElabEnv shape ret locals labels -> ElabEnv shape ret locals (rs ': labels)
pushLabel rsS env = env { eeLabels = LSCons rsS (eeLabels env) }

-- | Elaborate a block/loop/if body (its label already pushed onto @env@), checking it
--   transforms @ps@ into @rs@, and hand the resulting typed sequence to the continuation.
elabBodyChecked
    :: ElabEnv shape ret locals labels
    -> StackS ps -> StackS rs -> [RawInstr]
    -> (Expr shape ret locals labels ps rs -> Either ElabError a)
    -> Either ElabError a
elabBodyChecked env psS rsS body k = do
    body' <- elabSeq env psS body
    case body' of
        Reachable soS seq' -> do
            Refl <- note (ResultMismatch "body result does not match its block type") (decideStack soS rsS)
            k seq'
        Diverged poly -> k poly

-- | Resolve one @br_table@ target, checking it carries the same result type as the rest.
resolveTarget :: ElabEnv shape ret locals labels -> StackS rs -> LabelIdx -> Either ElabError (Elem rs labels)
resolveTarget env rsS (LabelIdx t) = case mkLabelElem (eeLabels env) t of
    Nothing -> Left (IndexOutOfRange ("br_table target " ++ show t))
    Just (SomeLabel rsS' targetIx) -> case decideStack rsS' rsS of
        Just Refl -> Right targetIx
        Nothing   -> Left (TypeMismatch "br_table targets have different types")

-- | Check the top two operands are both @'Num t@ and replace them with the instruction's
--   single result of element type @r@.
-- | Refine an operation's number type to integer (resp. floating-point) evidence, failing
--   elaboration if it is of the wrong kind (e.g. @f32.and@ or @i32.sqrt@). This is what
--   lets the typed interpreter dispatch those instructions totally, with no float/int
--   fall-through to reject at run time.
withInt :: SNumType t -> (IsInt t -> Either ElabError a) -> Either ElabError a
withInt st k = maybe (Left (TypeMismatch "operation requires an integer type")) k (intType st)

withFloat :: SNumType t -> (IsFloat t -> Either ElabError a) -> Either ElabError a
withFloat st k = maybe (Left (TypeMismatch "operation requires a floating-point type")) k (floatType st)

consumeTwo :: forall t r shape ret locals labels si.
              SNumType t -> SValType r -> StackS si
           -> (forall s. Instr shape ret locals labels ('Num t ': 'Num t ': s) (r ': s))
           -> Either ElabError (Step shape ret locals labels si)
consumeTwo st sr si typed = case si of
    SSCons (SNum sa) (SSCons (SNum sb) rest) -> do
        Refl <- note (TypeMismatch "binary op operand 1") (decideNumType sa st)
        Refl <- note (TypeMismatch "binary op operand 2") (decideNumType sb st)
        Right (StepTo (SSCons sr rest) typed)
    _ -> Left (StackUnderflow "binary numeric op")

-- | A binary operation whose result has the same type as its (matching) operands.
sameTypeBinary :: SNumType t -> StackS si
               -> (forall s. Instr shape ret locals labels ('Num t ': 'Num t ': s) ('Num t ': s))
               -> Either ElabError (Step shape ret locals labels si)
sameTypeBinary st = consumeTwo st (SNum st)

-- | A unary operation whose result has the same type as its operand.
sameTypeUnary :: SNumType t -> StackS si
              -> (forall s. Instr shape ret locals labels ('Num t ': s) ('Num t ': s))
              -> Either ElabError (Step shape ret locals labels si)
sameTypeUnary st si typed = case si of
    SSCons (SNum sa) rest -> do
        Refl <- note (TypeMismatch "unary op operand") (decideNumType sa st)
        Right (StepTo (SSCons (SNum st) rest) typed)
    _ -> Left (StackUnderflow "unary numeric op")

{- *** Unreachable code (full unreachable typing) ***

   After an unconditional transfer the operand stack becomes polymorphic. We validate the
   dead tail over a 'PolyStack' — known entries above an implicit @Unknown@ bottom — so
   underflowing pops yield @Unknown@ (and succeed), exactly as the spec prescribes. Nested
   block/loop/if bodies are fresh reachable frames, validated by the ordinary elaborator. -}

newtype PolyStack = PolyStack [Maybe ValType]

pushKnown :: ValType -> PolyStack -> PolyStack
pushKnown v (PolyStack xs) = PolyStack (Just v : xs)

popAny :: PolyStack -> (Maybe ValType, PolyStack)
popAny (PolyStack (x : xs)) = (x, PolyStack xs)
popAny (PolyStack [])       = (Nothing, PolyStack [])

popKnown :: ValType -> PolyStack -> Either ElabError PolyStack
popKnown t s = case popAny s of
    (Nothing, s')             -> Right s'
    (Just v,  s') | v == t    -> Right s'
                  | otherwise -> Left (DeadCodeError msg)
      where msg = "unreachable code expected " ++ show t ++ ", found " ++ show v

validateDead :: ElabEnv shape ret locals labels -> [RawInstr] -> Either ElabError ()
validateDead env = go (PolyStack [])
  where
    go _ []       = Right ()
    go s (i : is) = stepDead env s i >>= \s' -> go s' is

stepDead :: ElabEnv shape ret locals labels -> PolyStack -> RawInstr -> Either ElabError PolyStack
stepDead env s instr = case instr of
    Const t _  -> Right (pushKnown (numVal t) s)
    Add t      -> arith t
    Sub t      -> arith t
    Mul t      -> arith t
    Div t _    -> arith t
    Rem t _    -> arith t
    Eq  t      -> compare' t
    Ne  t      -> compare' t
    Lt  t _    -> compare' t
    Gt  t _    -> compare' t
    Le  t _    -> compare' t
    Ge  t _    -> compare' t
    Eqz t      -> pushKnown (Num I32) <$> popKnown (numVal t) s
    Drop       -> Right (snd (popAny s))
    Select     -> do
        s1 <- popKnown (Num I32) s
        let (a, s2) = popAny s1
            (b, s3) = popAny s2
        Right (PolyStack (orElse a b : unStack s3))
    LocalGet (LocalIdx i) -> withLocal env i (\v -> Right (pushKnown v s))
    LocalSet (LocalIdx i) -> withLocal env i (\v -> popKnown v s)
    LocalTee (LocalIdx i) -> withLocal env i (\v -> pushKnown v <$> popKnown v s)
    GlobalGet (GlobalIdx g) -> case lookupGlobalRef (shapeGlobalsS (eeShape env)) g of
        Nothing                       -> Left (IndexOutOfRange ("global.get " ++ show g ++ " (unreachable)"))
        Just (SomeGlobalRef _ st _)   -> Right (pushKnown (numValOf st) s)
    GlobalSet (GlobalIdx g) -> case lookupGlobalRef (shapeGlobalsS (eeShape env)) g of
        Nothing                       -> Left (IndexOutOfRange ("global.set " ++ show g ++ " (unreachable)"))
        Just (SomeGlobalRef _ st _)   -> popKnown (numValOf st) s
    Load t _   -> pushKnown (numVal t) <$> popKnown (Num I32) s
    Store t _  -> popKnown (numVal t) s >>= popKnown (Num I32)
    LoadN t _ _ _  -> pushKnown (numVal t) <$> popKnown (Num I32) s
    StoreN t _ _   -> popKnown (numVal t) s >>= popKnown (Num I32)
    MemorySize     -> Right (pushKnown (Num I32) s)
    MemoryGrow     -> pushKnown (Num I32) <$> popKnown (Num I32) s
    And t      -> arith t
    Or  t      -> arith t
    Xor t      -> arith t
    Shl t      -> arith t
    Shr t _    -> arith t
    Rotl t     -> arith t
    Rotr t     -> arith t
    Clz t      -> sameUnary t
    Ctz t      -> sameUnary t
    Popcnt t   -> sameUnary t
    Abs t        -> sameUnary t
    Neg t        -> sameUnary t
    Sqrt t       -> sameUnary t
    Ceil t       -> sameUnary t
    Floor t      -> sameUnary t
    FloatTrunc t -> sameUnary t
    Nearest t    -> sameUnary t
    Min t        -> arith t
    Max t        -> arith t
    Copysign t   -> arith t
    Convert op   -> let (from, to) = convertSig op in pushKnown to <$> popKnown from s
    Call (FunctionIdx f) -> case lookupFuncRef (shapeFuncsS (eeShape env)) f of
        Nothing                     -> Left (IndexOutOfRange ("call " ++ show f ++ " (unreachable)"))
        Just (SomeFuncRef psS rsS _) -> afterFrame (stackToList psS) (stackToList rsS) s
    Nop        -> Right s
    Block (FuncType psT rsT) body -> validateFrame env rsT psT rsT body >> afterFrame psT rsT s
    Loop  (FuncType psT rsT) body -> validateFrame env psT psT rsT body >> afterFrame psT rsT s
    If (FuncType psT rsT) thenB elseB -> do
        s1 <- popKnown (Num I32) s
        validateFrame env rsT psT rsT thenB
        validateFrame env rsT psT rsT elseB
        afterFrame psT rsT s1
    Br (LabelIdx l)        -> checkLabel env l >> Right s
    BrIf (LabelIdx l)      -> popKnown (Num I32) s >>= \s' -> checkLabel env l >> Right s'
    BrTable targets (LabelIdx d) -> do
        s' <- popKnown (Num I32) s
        mapM_ (\(LabelIdx t) -> checkLabel env t) targets
        checkLabel env d
        Right s'
    Return     -> Right s
    Unreachable -> Right s
  where
    arith :: SNumType t -> Either ElabError PolyStack
    arith t = pushKnown (numVal t) <$> (popKnown (numVal t) s >>= popKnown (numVal t))
    compare' :: SNumType t -> Either ElabError PolyStack
    compare' t = pushKnown (Num I32) <$> (popKnown (numVal t) s >>= popKnown (numVal t))
    sameUnary :: SNumType t -> Either ElabError PolyStack
    sameUnary t = pushKnown (numVal t) <$> popKnown (numVal t) s

data SomeNum where
    SomeNum :: SNumType n -> SomeNum

reflectNum :: NumType -> SomeNum
reflectNum I32 = SomeNum SI32
reflectNum I64 = SomeNum SI64
reflectNum F32 = SomeNum SF32
reflectNum F64 = SomeNum SF64

-- | The source and result value types of a conversion (for dead-code validation).
convertSig :: ConvertOp -> (ValType, ValType)
convertSig op = case op of
    I32WrapI64        -> (Num I64, Num I32)
    I64ExtendI32 _    -> (Num I32, Num I64)
    I32TruncF32 _     -> (Num F32, Num I32)
    I32TruncF64 _     -> (Num F64, Num I32)
    I64TruncF32 _     -> (Num F32, Num I64)
    I64TruncF64 _     -> (Num F64, Num I64)
    F32ConvertI32 _   -> (Num I32, Num F32)
    F32ConvertI64 _   -> (Num I64, Num F32)
    F64ConvertI32 _   -> (Num I32, Num F64)
    F64ConvertI64 _   -> (Num I64, Num F64)
    F32DemoteF64      -> (Num F64, Num F32)
    F64PromoteF32     -> (Num F32, Num F64)
    I32ReinterpretF32 -> (Num F32, Num I32)
    F32ReinterpretI32 -> (Num I32, Num F32)
    I64ReinterpretF64 -> (Num F64, Num I64)
    F64ReinterpretI64 -> (Num I64, Num F64)
    I32Extend8S       -> (Num I32, Num I32)
    I32Extend16S      -> (Num I32, Num I32)
    I64Extend8S       -> (Num I64, Num I64)
    I64Extend16S      -> (Num I64, Num I64)
    I64Extend32S      -> (Num I64, Num I64)

-- | Validate a nested block/loop/if body — a fresh, reachable frame — discarding its AST.
validateFrame :: ElabEnv shape ret locals labels
              -> [ValType] -> [ValType] -> [ValType] -> [RawInstr] -> Either ElabError ()
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
withLocal env i k = case mkLocalElem (eeLocals env) i of
    Just (SomeElem sv _) -> k (numValOf sv)
    Nothing              -> Left (IndexOutOfRange ("local " ++ show i ++ " (unreachable code)"))

checkLabel :: ElabEnv shape ret locals labels -> Word32 -> Either ElabError ()
checkLabel env l = case mkLabelElem (eeLabels env) l of
    Just _  -> Right ()
    Nothing -> Left (IndexOutOfRange ("label " ++ show l ++ " (unreachable code)"))

numVal :: SNumType t -> ValType
numVal SI32 = Num I32
numVal SI64 = Num I64
numVal SF32 = Num F32
numVal SF64 = Num F64

numValOf :: SValType v -> ValType
numValOf (SNum n) = numVal n

stackToList :: StackS s -> [ValType]
stackToList SSNil         = []
stackToList (SSCons v vs) = numValOf v : stackToList vs

orElse :: Maybe a -> Maybe a -> Maybe a
orElse (Just x) _ = Just x
orElse Nothing  y = y

unStack :: PolyStack -> [Maybe ValType]
unStack (PolyStack xs) = xs

{- *** Whole-module elaboration *** -}

-- | A fully elaborated, well-typed module: its signature witness, its typed instances, and
--   its exports (for resolving entry points).
data SomeModule where
    SomeModule :: ModuleShapeS shape -> ModuleInst shape -> [Export] -> SomeModule

-- | Type-check an entire decoded module: build its signature, elaborate every function
--   against it, and assemble the typed functions, initial globals and memories.
elaborateModule :: RawModule -> Either ElabError SomeModule
elaborateModule m =
    case reflectCtx funcSigs globalTypes memTypes of
        SomeModuleShapeS ctxS@(ModuleShapeS ftsS gsS msS) -> do
            funcs   <- elaborateFuncs ctxS ftsS (moduleFuncs m)
            globals <- buildGlobals gsS (moduleGlobals m)
            mems    <- buildMems msS (moduleMemories m)
            Right (SomeModule ctxS (ModuleInst funcs globals mems) (moduleExports m))
  where
    funcSigs    = map (\(RawFunction sig _ _) -> sig) (moduleFuncs m)
    globalTypes = map (\(RawGlobal gt _) -> gt) (moduleGlobals m)
    memTypes    = map (\(RawMemory mt) -> mt) (moduleMemories m)

elaborateFuncs :: ModuleShapeS shape -> FuncTypesS fts -> [RawFunction] -> Either ElabError (FuncInsts shape fts)
elaborateFuncs _    FtSNil          []          = Right FsNil
elaborateFuncs ctxS (FtSCons ft fs) (rf : rfs)  = do
    f  <- elaborateFunctionIn ctxS ft rf
    fs' <- elaborateFuncs ctxS fs rfs
    Right (FsCons f fs')
elaborateFuncs _ _ _ = Left (Malformed "function/signature count mismatch")

elaborateFunctionIn :: ModuleShapeS shape -> FuncTypeS ft -> RawFunction
                    -> Either ElabError (FuncInst shape ft)
elaborateFunctionIn ctxS (FuncTypeS psS rsS) (RawFunction _ declaredT body) =
    case reflectStack declaredT of
        SomeStack declS ->
            let env      = ElabEnv ctxS rsS (sAppendS psS declS) (LSCons rsS LSNil)
                defaults = defaultLocals declS
            in do
                elaborated <- elabSeq env SSNil body
                case elaborated of
                    Reachable soS bodySeq -> do
                        Refl <- note (ResultMismatch "function body does not match its result type")
                                     (decideStack soS rsS)
                        Right (FuncInst defaults bodySeq)
                    Diverged poly -> Right (FuncInst defaults poly)

buildGlobals :: GlobalsS gs -> [RawGlobal] -> Either ElabError (GlobalInsts gs)
buildGlobals GsSNil [] = Right GNil
buildGlobals (GsSCons (GlobalTypeS _ (SNum sn)) gs) (RawGlobal _ initExpr : rest) = do
    value <- evalConstInit sn initExpr
    rest' <- buildGlobals gs rest
    Right (GCons value rest')
buildGlobals _ _ = Left (Malformed "global/type count mismatch")

evalConstInit :: SNumType n -> [RawInstr] -> Either ElabError (RuntimeHostType ('Num n))
evalConstInit sn [Const st literal] = case decideNumType st sn of
    Just Refl -> Right literal
    Nothing   -> Left (TypeMismatch "global initializer type mismatch")
evalConstInit _ _ = Left (UnsupportedInstr "non-constant global initializer")

-- | Build the runtime memories matching the module's declared memory shapes, each allocated
--   at its minimum page count.
buildMems :: MemsS ms -> [RawMemory] -> Either ElabError (MemInsts ms)
buildMems MsSNil           []                                                = Right MNil
buildMems (MsSCons _ rest) (RawMemory (MemType _ (Limits minPages _)) : rms) =
    MCons (allocMemory minPages) <$> buildMems rest rms
buildMems _ _ = Left (Malformed "memory/type count mismatch")

-- | Zero-initialise a locals frame of the given shape.
defaultLocals :: StackS ds -> LocalInsts ds
defaultLocals SSNil                 = LNil
defaultLocals (SSCons (SNum sn) ds) = zeroOf sn :& defaultLocals ds

zeroOf :: SNumType n -> RuntimeHostType ('Num n)
zeroOf SI32 = 0
zeroOf SI64 = 0
zeroOf SF32 = 0
zeroOf SF64 = 0

{- *** Running an exported function *** -}

-- | Resolve an export, build a typed argument stack from integer literals, run the
--   function on the module, and render the results.
runModuleFunction :: SomeModule -> Text -> [Integer] -> Either String [String]
runModuleFunction (SomeModule ctxS typedModule exports) name args =
    case exportedFuncIndex name exports of
        Nothing -> Left ("no exported function named " ++ T.unpack name)
        Just (FunctionIdx idx) -> case lookupFuncRef (shapeFuncsS ctxS) idx of
            Nothing -> Left "exported function index out of range"
            Just (SomeFuncRef paramsS resultsS funcIx) -> do
                argStack <- buildArgs paramsS args
                case runFunction typedModule (getFunc funcIx (miFuncs typedModule)) argStack of
                    Left aTrap -> Left ("trap: " ++ show aTrap)
                    Right vals -> Right (renderResults resultsS vals)

exportedFuncIndex :: Text -> [Export] -> Maybe FunctionIdx
exportedFuncIndex name exports =
    case [idx | Export n (ExportFunc idx) <- exports, n == name] of
        (idx : _) -> Just idx
        []        -> Nothing

buildArgs :: StackS ps -> [Integer] -> Either String (ValueStack ps)
buildArgs SSNil                []       = Right VNil
buildArgs SSNil                _        = Left "too many arguments"
buildArgs (SSCons _ _)         []       = Left "too few arguments"
buildArgs (SSCons (SNum sn) r) (a : as) = (fromIntegerOf sn a :#) <$> buildArgs r as

renderResults :: StackS rs -> ValueStack rs -> [String]
renderResults SSNil                VNil      = []
renderResults (SSCons (SNum sn) r) (v :# vs) = showOf sn v : renderResults r vs

fromIntegerOf :: SNumType n -> Integer -> RuntimeHostType ('Num n)
fromIntegerOf SI32 = fromInteger
fromIntegerOf SI64 = fromInteger
fromIntegerOf SF32 = fromInteger
fromIntegerOf SF64 = fromInteger

showOf :: SNumType n -> RuntimeHostType ('Num n) -> String
showOf SI32 = show
showOf SI64 = show
showOf SF32 = show
showOf SF64 = show
