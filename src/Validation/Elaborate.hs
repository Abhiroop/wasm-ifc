{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
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
    Raise (..),
    BlockRaise (..),
    OperandKind (..),
    IndexSpace (..),
    elaborateModule,
    elaborateModuleWith,
    Inferred (..),
    elaborateModuleInferring,
    elaborateModuleTraced,
) where

import Control.Monad (foldM, when)
import Data.Bifunctor (first)
import Data.Text (Text)
import Data.Type.Equality ((:~:) (Refl))
import Data.Word (Word32)

import Data.List.Singletons ((%++))
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
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
    FallThrough (..),
    FloatBinOp (..),
    FloatUnOp (..),
    Instr (..),
    RawInstr (..),
    convertEnds,
 )
import Syntax.Module
import Syntax.Types
import Syntax.TypesIFC
import Validation.LocalWebs (splitModuleLocals)
import Validation.Policy (Assembled (..), LocalSplitting (..), Policy, PolicyError, Restrictions (..), assemble, emptyPolicy, modulePolicy)
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
    | {- | a level annotation or a site on an instruction that takes none, or a load without a
      site: a mistake of the policy stage
      -}
      AnnotationMisplaced
    | -- | @declassify@ in a module whose policy does not allow it
      DeclassifyNotAllowed
    | -- | the security policy could not be read or does not fit the module
      BadPolicy PolicyError
    | {- | an 'IllegalFlow' that raising these labels, which inference chose, may repair (see
      'elaborateModuleWith')
      -}
      LevelTooLow [Raise] ElabError
    | {- | where the error arose: the instruction's position in its function's body, counting
      every instruction in code order from zero (a block, loop or @if@ counts once and before
      its body, an @else@ arm after its @then@ arm, @end@ and @else@ not at all; the order in
      which @wasm2wat@ lists them)
      -}
      AtInstruction Int ElabError
    | -- | the function, by index, in whose body the error arose
      InFunction Word32 ElabError
    | {- | an 'IllegalFlow' that a label the validator chose for an enclosing block, loop or
      @if@ may repair by being secret; it never leaves the function it arose in
      -}
      BlockTooLow BlockRaise ElabError
    deriving stock (Eq, Show)

{- | What the validator chose for a block, loop or @if@ and may choose higher: the labels of its
  own results, the pc a loop's body is checked at, or the types of the labels a branch names,
  by their depth from the branch (0 is the innermost).
-}
data BlockRaise = OwnResults | LoopPc | LabelsAt [Word32]
    deriving stock (Eq, Show)

{- | A label that inference chose and may raise: of a local variable (by its index in the
  function's local space, parameters first), or of an internal function's parameter or result
  (by its declared position) or its bound. Each names the function by its index.
-}
data Raise
    = RaiseLocal Word32 Word32
    | RaiseParam Word32 Int
    | RaiseResult Word32 Int
    | RaiseBound Word32
    deriving stock (Eq, Ord, Show)

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
data ElabEnv (shape :: ModuleShape) (ret :: LabelledResultType) (locals :: [LabelledValType]) (labels :: [LabelledResultType]) = ElabEnv
    { shape :: Sing shape
    , types :: [LabelledFuncType]
    -- ^ the module's type section as the policy labels it, which @call_indirect@ refers into
    , results :: Sing ret
    , locals :: Sing locals
    , labels :: Sing labels
    , loadDefault :: SecLevel
    -- ^ the level a load declares when nothing annotates it (see "Validation.Policy")
    , declassifyAllowed :: Bool
    -- ^ whether the policy enables 'Declassify'
    , restrictions :: Restrictions
    -- ^ whether calls and @br_if@ follow SecWasm's restrictions (see "Validation.Policy")
    , functionIndex :: Word32
    -- ^ the index of the function being elaborated, which the raises of inference name
    , firstPosition :: Int
    -- ^ the position (see 'AtInstruction') of the first instruction of the sequence elaborated
    , position :: Int
    -- ^ the position of the instruction elaborated
    }

{- | The result of elaborating a whole instruction sequence that started from pc stack @pcIn@
  and stack @stackIn@. It always says where the pc stack ended up (and that it kept its length,
  see 'SameLength'). A sequence either runs to its end or leaves early through an unconditional
  branch, and the two cases carry different evidence:
-}
data ElaboratedExpr (shape :: ModuleShape) (ret :: LabelledResultType) (locals :: [LabelledValType]) (labels :: [LabelledResultType]) (pcIn :: PcStack) (stackIn :: [LabelledValType]) where
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
data ElaboratedInstr (shape :: ModuleShape) (ret :: LabelledResultType) (locals :: [LabelledValType]) (labels :: [LabelledResultType]) (pcIn :: PcStack) (stackIn :: [LabelledValType]) where
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

{- | An 'IllegalFlow' as one these raises may repair ('LevelTooLow'); any other error, or no
  raise, as it is.
-}
blame :: [Raise] -> Either ElabError a -> Either ElabError a
blame raises result = case result of
    Left err@(IllegalFlow {}) | not (null raises) -> Left (LevelTooLow raises err)
    _ -> result

{- | The raises that let the values @carried@ (top first) meet the labels @expected@ of a
  function's parameters or results (in stack order): one for each position where a secret
  value meets a public label, named by its declared position.
-}
raisesWhereBelow :: (Int -> Raise) -> Sing (expected :: [LabelledValType]) -> Sing (carried :: [LabelledValType]) -> [Raise]
raisesWhereBelow raise expected carried =
    [raise (count - 1 - k) | (k, (_ :~ le, _ :~ lc)) <- zip [0 ..] (zip labels (fromSing carried)), le == Low, lc == High]
  where
    labels = fromSing expected
    count = length labels

-- | The raises that make every label of a function's parameters or results at least @level@.
raisesToAtLeast :: (Int -> Raise) -> Sing (level :: SecLevel) -> Sing (expected :: [LabelledValType]) -> [Raise]
raisesToAtLeast raise level expected = case fromSing level of
    Low -> []
    High -> [raise (count - 1 - k) | (k, _ :~ Low) <- zip [0 ..] labels]
  where
    labels = fromSing expected
    count = length labels

{- | An 'IllegalFlow' of the values a branch carries, as what may repair it: the function's
  results (the given raises), if one of its targets is the function body's own label, the
  outermost, whose type they are; otherwise the types of the labels it names, which the
  blocks that own them chose.
-}
blameBranch :: ElabEnv shape ret locals labels -> [Word32] -> [Raise] -> Either ElabError a -> Either ElabError a
blameBranch env targets raises result
    | outermost `elem` targets = blame raises result
    | otherwise = forBlock (LabelsAt targets) result
  where
    outermost = fromIntegral (length (fromSing env.labels)) - 1

-- | An 'IllegalFlow' as one that a choice of an enclosing block may repair ('BlockTooLow').
forBlock :: BlockRaise -> Either ElabError a -> Either ElabError a
forBlock raise result = case result of
    Left err@(IllegalFlow {}) -> Left (BlockTooLow raise err)
    _ -> result

{- | An error as the instructions around a block see it: one about the block's own choices is
  final once the block has tried both, and one about the labels a branch names is one label
  nearer.
-}
leaveBlock :: ElabError -> ElabError
leaveBlock err = case err of
    BlockTooLow (LabelsAt depths) inner -> case [depth - 1 | depth <- depths, depth > 0] of
        [] -> inner
        outer -> BlockTooLow (LabelsAt outer) inner
    BlockTooLow _ inner -> inner
    _ -> err

-- | Whether raising the results of the block the error has just reached may repair it.
aboutOwnResults :: ElabError -> Bool
aboutOwnResults err = case err of
    BlockTooLow OwnResults _ -> True
    _ -> False

-- | Whether raising the type of the label of the block the error has just reached may repair it.
aboutOwnLabel :: ElabError -> Bool
aboutOwnLabel err = case err of
    BlockTooLow (LabelsAt depths) _ -> 0 `elem` depths
    _ -> False

-- | Require that the values a branch carries are at least as secret as the decision to branch.
requireCarried :: Text -> Sing (l :: SecLevel) -> Sing (rs :: [LabelledValType]) -> Either ElabError (AllAtLeast l rs)
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
    elaboratedInstr <- first (placeAt env.firstPosition) (elabInstr env {position = env.firstPosition} pcs stackIn raw)
    case elaboratedInstr of
        Produces same@(BothLonger _) pcs'@(SCons _ _) stackOut instr -> do
            rest' <- elabSeq env {firstPosition = env.firstPosition + instructionCount raw} pcs' stackOut rest
            pure $ case rest' of
                Reachable same' pcOut stackOut' seq' -> Reachable (thenSameLength same same') pcOut stackOut' (instr :. seq')
                Diverged same' pcOut final poly -> Diverged (thenSameLength same same') pcOut final (instr :. poly)
        Transfers same pcOut transfer -> do
            final <- validateDead env pcs rest
            pure (Diverged same pcOut final (transfer :. INil))

{- | An error placed at an instruction, unless an instruction nested in it already placed it; a
  'LevelTooLow' stays outermost, where inference looks for it.
-}
placeAt :: Int -> ElabError -> ElabError
placeAt here err = case err of
    LevelTooLow raises inner -> LevelTooLow raises (placeAt here inner)
    BlockTooLow raise inner -> BlockTooLow raise (placeAt here inner)
    AtInstruction {} -> err
    _ -> AtInstruction here err

-- | An error placed in a function (see 'placeAt').
placeIn :: Word32 -> ElabError -> ElabError
placeIn function err = case err of
    LevelTooLow raises inner -> LevelTooLow raises (placeIn function inner)
    BlockTooLow _ inner -> placeIn function inner
    _ -> InFunction function err

-- | How many instructions an instruction is in the count of 'AtInstruction': itself and its bodies.
instructionCount :: RawInstr -> Int
instructionCount raw = case raw of
    Block _ body -> 1 + sum (map instructionCount body)
    Loop _ body -> 1 + sum (map instructionCount body)
    If _ thenBody elseBody -> 1 + sum (map instructionCount thenBody) + sum (map instructionCount elseBody)
    _ -> 1

-- | The environment of a body that starts right after the instruction elaborated, or after the given instructions (an @else@ arm, after its @then@ arm).
bodyAfter :: [RawInstr] -> ElabEnv shape ret locals labels -> ElabEnv shape ret locals labels
bodyAfter before env = env {firstPosition = env.position + 1 + sum (map instructionCount before)}

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
                pcFlows <- blame [RaiseLocal env.functionIndex i] (requireFlow "local.set" pc lvar)
                valueFlows <- blame [RaiseLocal env.functionIndex i] (requireFlow "local.set" lv lvar)
                Right (Produces (sameLengthAs pcsIn) pcsIn rest (ILocalSet pcFlows valueFlows (resolveLocal sv ix)))
            _ -> Left (StackUnderflow "local.set")
        Nothing -> Left (IndexOutOfRange Locals i)
    LocalTee (LocalIdx i) -> case mkLocalElem (env.locals) i of
        Just (SomeElem sv@(svt :%~ lvar) ix) -> case stackIn of
            SCons (stop :%~ lv) _ -> do
                Refl <- note (OperandMismatch "local.tee" (valTypeOf svt) (valTypeOf stop)) (decideEquality stop svt)
                pcFlows <- blame [RaiseLocal env.functionIndex i] (requireFlow "local.tee" pc lvar)
                valueFlows <- blame [RaiseLocal env.functionIndex i] (requireFlow "local.tee" lv lvar)
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
    Load st memArg -> elabMemory env pcsIn stackIn Nothing Nothing (Load st memArg)
    Store st memArg -> elabMemory env pcsIn stackIn Nothing Nothing (Store st memArg)
    LoadN st width sign memArg -> elabMemory env pcsIn stackIn Nothing Nothing (LoadN st width sign memArg)
    StoreN st width memArg -> elabMemory env pcsIn stackIn Nothing Nothing (StoreN st width memArg)
    Annotated level access -> elabMemory env pcsIn stackIn (Just level) Nothing access
    AtSite site (Annotated level access) -> elabMemory env pcsIn stackIn (Just level) (Just site) access
    AtSite site access -> elabMemory env pcsIn stackIn Nothing (Just site) access
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
            expected <- note (IndexOutOfRange Types t) (nth (env.types) t)
            case toSing (stackOrderLabelled expected) of
                SomeSing (SLabelledFuncType boundS psS rsS) -> do
                    SomeCoercion sS flows witness <- prefixFlows "call_indirect" psS rest
                    calledFrom <- requireFlow "call_indirect" (sJoin pc lidx) boundS
                    atCallPc <- argumentsAtCallPc env "call_indirect" pc psS
                    Right (Produces (sameLengthAs pcsIn) pcsIn (rsS %++ sS) (ICallIndirect calledFrom flows atCallPc witness (SLabelledFuncType boundS psS rsS)))
        _ -> Left (StackUnderflow "call_indirect")
    Call (FunctionIdx f) -> case lookupFuncRef (funcTypesSing (env.shape)) f of
        Nothing -> Left (IndexOutOfRange Functions f)
        Just (SomeFuncRef boundS psS rsS fix) -> do
            SomeCoercion sS flows witness <- blame (raisesWhereBelow (RaiseParam f) psS stackIn) (prefixFlows "call" psS stackIn)
            calledFrom <- blame [RaiseBound f] (requireFlow "call" pc boundS)
            atCallPc <- blame (raisesToAtLeast (RaiseParam f) pc psS) (argumentsAtCallPc env "call" pc psS)
            Right (Produces (sameLengthAs pcsIn) pcsIn (rsS %++ sS) (ICall calledFrom flows atCallPc witness fix))
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
        first leaveBlock $ blockParams "block" psT stackIn $ \psS sS witness ->
            inferResults (\e -> aboutOwnResults e || aboutOwnLabel e) rsT pc $ \rsS ->
                elabBodyChecked (pushLabel rsS (bodyAfter [] env)) (SCons pc pcsIn) psS rsS body $ \(BodyResult (BothLonger same) (SCons pcBody pcsOut) bodySeq) -> do
                    atStart <- forBlock OwnResults (requireCarried "block result" pc rsS)
                    atEnd <- forBlock OwnResults (resultsAtEndPc env "block result" pcBody rsS)
                    Right (Produces same pcsOut (rsS %++ sS) (IBlock atStart atEnd (segmentSelf psS) witness bodySeq))
    Loop (FuncType psT rsT) body ->
        first leaveBlock $ blockParams "loop" psT stackIn $ \psIn sS witness ->
            loopParams psIn $ \psS entry ->
                loopAt pc $ \pcLoop entryFlows ->
                    inferResults aboutOwnResults rsT pcLoop $ \rsS ->
                        elabBodyChecked (pushLabel psS (bodyAfter [] env)) (SCons pcLoop pcsIn) psS rsS body $ \(BodyResult (BothLonger same) (SCons pcBody pcsOut) bodySeq) -> do
                            backFlows <- forBlock LoopPc (requireFlow "loop" pcBody pcLoop)
                            atStart <- forBlock OwnResults (requireCarried "loop result" pcLoop rsS)
                            Right (Produces same pcsOut (rsS %++ sS) (ILoop atStart entryFlows backFlows entry witness bodySeq))
    If (FuncType psT rsT) thenBody elseBody -> case stackIn of
        SCons (sc :%~ lc) rest -> do
            Refl <- note (OperandMismatch "if" I32 (valTypeOf sc)) (decideEquality sc SI32)
            first leaveBlock $ blockParams "if" psT rest $ \psS sS witness ->
                inferResults (\e -> aboutOwnResults e || aboutOwnLabel e) rsT (sJoin pc lc) $ \rsS ->
                    elabBodyChecked (pushLabel rsS (bodyAfter [] env)) (SCons (sJoin pc lc) pcsIn) psS rsS thenBody $ \(BodyResult (BothLonger sameThen) (SCons pcThen pcsThen) thenSeq) ->
                        elabBodyChecked (pushLabel rsS (bodyAfter thenBody env)) (SCons (sJoin pc lc) pcsIn) psS rsS elseBody $ \(BodyResult (BothLonger sameElse) (SCons pcElse pcsElse) elseSeq) -> do
                            atStart <- forBlock OwnResults (requireCarried "if result" (sJoin pc lc) rsS)
                            atEnd <- forBlock OwnResults (resultsAtEndPc env "if result" (sJoin pcThen pcElse) rsS)
                            Right (Produces (joinEachSameLength sameThen sameElse) (sJoinEach pcsThen pcsElse) (rsS %++ sS) (IIf atStart atEnd (segmentSelf psS) witness thenSeq elseSeq))
        _ -> Left (StackUnderflow "if")
    {- Branches (unconditional ones diverge). What a branch carries may be lower than the label's
       types; the witness relabels it on the way. -}
    Br (LabelIdx l) -> case mkBranchTarget pc (env.labels) pcsIn l of
        Nothing -> Left (IndexOutOfRange Labels l)
        Just (SomeBranchTarget rsS pcsOut same target) -> do
            SomeCoercion _ flows witness <- blameBranch env [l] (raisesWhereBelow (RaiseResult env.functionIndex) rsS stackIn) (prefixFlows "br" rsS stackIn)
            carried <- blameBranch env [l] (raisesToAtLeast (RaiseResult env.functionIndex) pc rsS) (requireCarried "br" pc rsS)
            Right (Transfers same pcsOut (IBr carried flows witness target))
    BrIf (LabelIdx l) -> case stackIn of
        SCons (sc :%~ lc) rest -> do
            Refl <- note (OperandMismatch "br_if" I32 (valTypeOf sc)) (decideEquality sc SI32)
            case mkBranchTarget (sJoin pc lc) (env.labels) pcsIn l of
                Nothing -> Left (IndexOutOfRange Labels l)
                Just (SomeBranchTarget rsS pcsOut same target) -> do
                    SomeCoercion sS flows witness <- blameBranch env [l] (raisesWhereBelow (RaiseResult env.functionIndex) rsS rest) (prefixFlows "br_if" rsS rest)
                    carried <- blameBranch env [l] (raisesToAtLeast (RaiseResult env.functionIndex) (sJoin pc lc) rsS) (requireCarried "br_if" (sJoin pc lc) rsS)
                    Right $ case env.restrictions of
                        LiftFree -> Produces same pcsOut rest (IBrIf carried flows witness KeepsLevels target)
                        SecWasmRestrictions -> Produces same pcsOut (rsS %++ sS) (IBrIf carried flows witness TakesTargetType target)
        _ -> Left (StackUnderflow "br_if")
    -- The table reaches down to its deepest target, default included.
    BrTable targets (LabelIdx d) ->
        let deepest = maximum (d : [t | LabelIdx t <- targets])
         in case stackIn of
                SCons (sc :%~ lc) rest -> case decideEquality sc SI32 of
                    Nothing -> Left (OperandMismatch "br_table" I32 (valTypeOf sc))
                    Just Refl -> case mkTableReach (sJoin pc lc) (env.labels) pcsIn deepest of
                        Nothing -> Left (IndexOutOfRange Labels deepest)
                        Just (SomeTableReach reachS pcsOut same reach) -> case mkLabelElem reachS d of
                            Nothing -> Left (IndexOutOfRange Labels d)
                            Just (SomeLabel rsS defIx) -> do
                                targetIxs <- mapM (resolveTarget reachS rsS) targets
                                SomeCoercion _ flows witness <- blameBranch env (d : [t | LabelIdx t <- targets]) (raisesWhereBelow (RaiseResult env.functionIndex) rsS rest) (prefixFlows "br_table" rsS rest)
                                carried <- blameBranch env (d : [t | LabelIdx t <- targets]) (raisesToAtLeast (RaiseResult env.functionIndex) (sJoin pc lc) rsS) (requireCarried "br_table" (sJoin pc lc) rsS)
                                Right (Transfers same pcsOut (IBrTable carried flows witness reach targetIxs defIx))
                _ -> Left (StackUnderflow "br_table")
    Return -> do
        SomeCoercion _ flows witness <- blame (raisesWhereBelow (RaiseResult env.functionIndex) env.results stackIn) (prefixFlows "return" (env.results) stackIn)
        carried <- blame (raisesToAtLeast (RaiseResult env.functionIndex) pc env.results) (requireCarried "return" pc (env.results))
        Right (Transfers (raiseAllSameLength pc pcsIn) (sRaiseAll pc pcsIn) (IReturn carried flows witness))
    Unreachable -> Right (Transfers (sameLengthAs pcsIn) pcsIn IUnreachable)

{- | The arguments of a call under the policy's restrictions: at any level without them, at
  least the pc at the call with them.
-}
argumentsAtCallPc :: ElabEnv shape ret locals labels -> Text -> Sing (pc :: SecLevel) -> Sing (ps :: [LabelledValType]) -> Either ElabError (ArgumentsAtCallPc pc ps)
argumentsAtCallPc env name pc psS = case env.restrictions of
    LiftFree -> Right ArgumentsAtAnyLevel
    SecWasmRestrictions -> ArgumentsAtLeastPc <$> requireCarried name pc psS

{- | The results of a block or conditional under the policy's restrictions: at any level
  without them, at least the pc the body ends with with them. A failure is one about levels,
  so the inference of the results tries secret ones next.
-}
resultsAtEndPc :: ElabEnv shape ret locals labels -> Text -> Sing (pcEnd :: SecLevel) -> Sing (rs :: [LabelledValType]) -> Either ElabError (ResultsAtEndPc pcEnd rs)
resultsAtEndPc env name pcEnd rsS = case env.restrictions of
    LiftFree -> Right ResultsAtAnyLevel
    SecWasmRestrictions -> ResultsAtLeastEndPc <$> requireCarried name pcEnd rsS

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
            ended <- forBlock OwnResults (endAt "block result" soS rsS seq')
            k (BodyResult same pcsOut ended)
        Diverged same pcsOut final poly -> do
            checkDeadResult final rsS
            k (BodyResult same pcsOut poly)

{- | A body that ended with stack @produced@ where @expected@ is required: unchanged when they
  agree, otherwise ended with a relabelling of its results to the levels expected, which they
  must flow into.
-}
endAt ::
    Text ->
    Sing (produced :: [LabelledValType]) ->
    Sing (expected :: [LabelledValType]) ->
    Expr shape frame labels pcIn pcOut stackIn produced ->
    Either ElabError (Expr shape frame labels pcIn pcOut stackIn expected)
endAt what produced expected body = case decideEquality produced expected of
    Just Refl -> Right body
    Nothing -> case decideSegmentFlows produced expected of
        Just flows -> Right (appendExpr body (IRelabelResults flows :. INil))
        Nothing
            | stackToList produced == stackToList expected -> Left (IllegalFlow what High Low)
            | otherwise -> Left (ResultMismatch (stackToList expected) (stackToList produced))

appendExpr :: Expr m f l p1 p2 s1 s2 -> Expr m f l p2 p3 s2 s3 -> Expr m f l p1 p3 s1 s3
appendExpr INil ys = ys
appendExpr (x :. xs) ys = x :. appendExpr xs ys

{- | The top of the stack as the segment a call, branch or return consumes: the value types
  must be the ones expected, and each level must flow into the one expected. With two levels
  the only flow that can fail is secret into public, which is what the error names.
-}
prefixFlows :: Text -> Sing (ps :: [LabelledValType]) -> Sing (full :: [LabelledValType]) -> Either ElabError (SomeCoercion ps full)
prefixFlows name psS stackS = case matchPrefixFlows psS stackS of
    Just coercion -> Right coercion
    Nothing
        | take (length expected) (stackToList stackS) == expected -> Left (IllegalFlow name High Low)
        | otherwise -> Left (StackMismatch name expected (stackToList stackS))
  where
    expected = stackToList psS

{- | The parameters a block takes off the stack: the top entries, whose value types must be
  the block type's. Their levels are whatever the stack holds; a decoded block type has none.
-}
blockParams ::
    Text ->
    [ValType] ->
    Sing (stackIn :: [LabelledValType]) ->
    (forall ps s. Sing ps -> Sing s -> Append ps s stackIn -> Either ElabError a) ->
    Either ElabError a
blockParams name psT stackIn k = case takePrefix (length psT) stackIn of
    Just (SomePrefix psS sS witness)
        | stackToList psS == stackOrder psT -> k psS sS witness
        | otherwise -> Left (StackMismatch name (stackOrder psT) (stackToList psS))
    Nothing -> Left (StackUnderflow name)

{- | The levels of a block's results, which a decoded block type does not say: the pc the body
  runs at first, since everything it pushes is at least that, and secret if the body turns out
  to produce or branch out with something more secret. Over two levels these are all the
  candidates, so this is a fixed point in at most two attempts. The second attempt is made
  only for a failure that secret results may repair (the predicate): any other failure would
  recur, and retrying it in every enclosing block would cost time exponential in the nesting.
-}
inferResults :: (ElabError -> Bool) -> [ValType] -> Sing (pc :: SecLevel) -> (forall rs. Sing (rs :: [LabelledValType]) -> Either ElabError a) -> Either ElabError a
inferResults repairable rsT pc k = case pc of
    SHigh -> attempt High
    SLow -> case attempt Low of
        Left e | repairable e -> attempt High
        result -> result
  where
    attempt level = case reflectStackAt level (stackOrder rsT) of
        SomeStack rsS -> k rsS

{- | The levels of a loop's parameters, which its label carries and a branch back must meet:
  the levels the entry values have, or secret if a branch back brings something more secret.
-}
loopParams ::
    Sing (psIn :: [LabelledValType]) ->
    (forall ps. Sing ps -> SegmentFlows psIn ps -> Either ElabError a) ->
    Either ElabError a
loopParams psIn k = case k psIn (segmentSelf psIn) of
    Left e | aboutOwnLabel e -> case reflectStackAt High (stackToList psIn) of
        SomeStack psHigh -> maybe (Left e) (k psHigh) (decideSegmentFlows psIn psHigh)
    result -> result

{- | The pc a loop body is checked at: the current pc if the body keeps it, and 'High if a
  branch inside raises it, because the body may run again under what it left. With two levels
  the second attempt always succeeds, so this is a fixed point in at most two steps.
-}
loopAt :: Sing (pc :: SecLevel) -> (forall pcLoop. Sing pcLoop -> FlowsInto pc pcLoop -> Either ElabError a) -> Either ElabError a
loopAt pc k = case k pc (case pc of SLow -> LowFlowsAnywhere; SHigh -> HighFlowsToHigh) of
    Left (BlockTooLow LoopPc _) -> k SHigh (case pc of SLow -> LowFlowsAnywhere; SHigh -> HighFlowsToHigh)
    result -> result

-- | Resolve one @br_table@ target within its reach, checking it carries the same result type as the rest.
resolveTarget :: Sing (reach :: [LabelledResultType]) -> Sing rs -> LabelIdx -> Either ElabError (Elem rs reach)
resolveTarget reachS rsS (LabelIdx t) = case mkLabelElem reachS t of
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
  (the join of the pc, the address and the value), which is always sound. A load also takes
  the site the policy stage gave it, which its trap names. An annotation on any other
  instruction, a site on anything but a load, and a load without one are mistakes of the policy
  stage.
-}
elabMemory ::
    forall shape ret locals labels pc pcs stackIn.
    ElabEnv shape ret locals labels ->
    Sing (pc ': pcs) ->
    Sing stackIn ->
    Maybe SecLevel ->
    Maybe AccessSite ->
    RawInstr ->
    Either ElabError (ElaboratedInstr shape ret locals labels (pc ': pcs) stackIn)
elabMemory env pcsIn@(SCons pc _) stackIn annotation site access = case access of
    Load st memArg -> case stackIn of
        SCons (sc :%~ la) rest -> do
            NonEmptyMems <- requireMemory env "load"
            isNum <- requireNum st
            Refl <- note (OperandMismatch "load" I32 (valTypeOf sc)) (decideEquality sc SI32)
            checkAlign memArg (numBytes isNum)
            loadSite <- note AnnotationMisplaced site
            withSomeSing loadLevel $ \level ->
                Right (Produces (sameLengthAs pcsIn) pcsIn (SCons (st :%~ sJoin pc (sJoin la level)) rest) (ILoad level loadSite isNum memArg))
        _ -> Left (StackUnderflow "load")
    LoadN st width sign memArg -> case stackIn of
        SCons (sc :%~ la) rest -> do
            NonEmptyMems <- requireMemory env "load"
            nw <- requireNarrow st width
            Refl <- note (OperandMismatch "load" I32 (valTypeOf sc)) (decideEquality sc SI32)
            checkAlign memArg (narrowBytes nw)
            loadSite <- note AnnotationMisplaced site
            withSomeSing loadLevel $ \level ->
                Right (Produces (sameLengthAs pcsIn) pcsIn (SCons (st :%~ sJoin pc (sJoin la level)) rest) (ILoadN level loadSite nw sign memArg))
        _ -> Left (StackUnderflow "load")
    Store st memArg -> case stackIn of
        SCons (sv :%~ lv) (SCons (sc :%~ la) rest) -> do
            NonEmptyMems <- requireMemory env "store"
            mapM_ (const (Left AnnotationMisplaced)) site
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
            mapM_ (const (Left AnnotationMisplaced)) site
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
checkDeadResult :: PolyStack -> Sing (rs :: [LabelledValType]) -> Either ElabError ()
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
    AtSite _ access -> stepDead env pcsIn s access
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
        Just (SomeFuncRef _ psS rsS _) -> afterFrame (stackToList psS) (stackToList rsS) s
    CallIndirect (TypeIdx t) -> do
        s1 <- popKnown I32 s
        LabelledFuncType _ ps rs <- note (IndexOutOfRange Types t) (nth (env.types) t)
        afterFrame (map unlabelled (stackOrder ps)) (map unlabelled (stackOrder rs)) s1
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
    orElseTry a b = either (const (first unblocked b)) Right a
    -- A choice that fails in dead code fails for good: no live block is to try again for it.
    unblocked err = case err of
        BlockTooLow _ inner -> inner
        _ -> err

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
unlabelledTypeOf :: Sing (t :: LabelledValType) -> ValType
unlabelledTypeOf = unlabelled . fromSing

stackToList :: Sing (s :: [LabelledValType]) -> [ValType]
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
  first, so every level the policy declares is settled before any function is checked; the
  levels it leaves to inference are settled by 'elaborateModuleInferring'.
-}
elaborateModuleWith :: Policy -> RawModule -> Either ElabError SomeModule
elaborateModuleWith given raw = fst <$> elaborateModuleInferring given raw

{- | What inference settled: the labels it raised from public. Locals are named by function
  and their index among the function's declared locals (after the parameters); an internal
  function by its index, with the type it ended with.
-}
data Inferred = Inferred
    { raisedLocals :: [(Word32, Word32)]
    , raisedFunctions :: [(Word32, LabelledFuncType)]
    , attempts :: Int
    -- ^ how many times the module was elaborated
    , history :: [[Raise]]
    -- ^ the raises of each attempt that failed and was repaired, in order
    }
    deriving stock (Eq, Show)

{- | The labels inference chooses and may raise: the function types (only those of internal
  functions ever change) and the levels of each defined function's declared locals.
-}
data Choices = Choices
    { chosenFunctionTypes :: [LabelledFuncType]
    , localLevels :: Map Word32 [SecLevel]
    }
    deriving stock (Eq)

{- | 'elaborateModuleWith', with a report of what inference raised. Inference chooses a label
  for every local variable and for the parameters, results and bound of every internal
  function (one the policy does not declare and nothing outside the module can call: not
  imported, exported, placed in a table or started). It starts with every such label public
  and elaborates the module; when a rule fails only because one of those labels is too low
  ('LevelTooLow'), it raises the labels the failure names and elaborates again. Labels only
  rise and there are finitely many, so this ends, with the least labels the typed rules
  accept, or with the first failure no raise repairs. Every accepted module is then checked
  by the same rules as a fully annotated one, so inference cannot make an insecure module
  typable. Raising a function's bound raises its results too, which must be at least the bound.
-}
elaborateModuleInferring :: Policy -> RawModule -> Either ElabError (SomeModule, Inferred)
elaborateModuleInferring given raw = case elaborateModuleTraced given raw of
    (inferred, result) -> fmap (,inferred) result

{- | 'elaborateModuleInferring', with the report of what inference raised whether or not the
  module is accepted in the end: what a user needs to see why it was not.
-}
elaborateModuleTraced :: Policy -> RawModule -> (Inferred, Either ElabError SomeModule)
elaborateModuleTraced given raw = case validateStructure raw >> first BadPolicy (modulePolicy given raw >>= (`assemble` raw)) of
    Left err -> (Inferred [] [] 0 [], Left err)
    Right assembledAsWritten ->
        -- Each web of a local gets a local of its own, and so a label of its own ("Validation.LocalWebs").
        let assembled = case assembledAsWritten.splitting of
                SplitIntoWebs -> assembledAsWritten {annotated = splitModuleLocals assembledAsWritten.annotated}
                LocalsAsWritten -> assembledAsWritten
            importCount = fromIntegral (length raw.imports)
            initial =
                Choices
                    { chosenFunctionTypes = assembled.functionTypes
                    , localLevels = Map.fromList [(i, map (const Low) declared) | (i, RawFunction _ declared _) <- zip [importCount ..] assembled.annotated.functions]
                    }
            settle count history choices = case elaborateUnder assembled choices of
                Right validated -> (report count history initial choices, Right validated)
                Left (LevelTooLow raises failure) -> case applyRaises assembled.inferableFunctions choices raises of
                    Just raised -> settle (count + 1) (history ++ [raises]) raised
                    Nothing -> (report count history initial choices, Left failure)
                Left failure -> (report count history initial choices, Left failure)
         in settle 1 [] initial
  where
    report count history initial final =
        Inferred
            { raisedLocals = [(f, i) | (f, levels) <- Map.toList final.localLevels, (i, High) <- zip [0 ..] levels]
            , raisedFunctions = [(f, after) | (f, before, after) <- zip3 [0 ..] initial.chosenFunctionTypes final.chosenFunctionTypes, before /= after]
            , attempts = count
            , history
            }

{- | Raise the labels a failure names, where inference chose them; 'Nothing' if none of them
  could rise, which leaves the failure standing.
-}
applyRaises :: [Bool] -> Choices -> [Raise] -> Maybe Choices
applyRaises inferable choices raises
    | raised == choices = Nothing
    | otherwise = Just raised
  where
    raised = foldl' raiseOne choices raises
    raiseOne current raise = case raise of
        RaiseLocal f i -> case paramCount f current of
            Just count
                | fromIntegral i < count -> raiseOne current (RaiseParam f (fromIntegral i))
                | otherwise -> current {localLevels = Map.adjust (setHigh (fromIntegral i - count)) f current.localLevels}
            Nothing -> current
        RaiseParam f j -> withType f current $ \(LabelledFuncType bound ps rs) -> LabelledFuncType bound (raiseAt j ps) rs
        RaiseResult f j -> withType f current $ \(LabelledFuncType bound ps rs) -> LabelledFuncType bound ps (raiseAt j rs)
        RaiseBound f -> withType f current $ \(LabelledFuncType _ ps rs) -> LabelledFuncType High ps [t :~ High | t :~ _ <- rs]
    paramCount f current = case drop (fromIntegral f) current.chosenFunctionTypes of
        LabelledFuncType _ ps _ : _ -> Just (length ps)
        [] -> Nothing
    withType f current change
        | fromIntegral f < length inferable && inferable !! fromIntegral f =
            current {chosenFunctionTypes = [if k == f then change ft else ft | (k, ft) <- zip [0 ..] current.chosenFunctionTypes]}
        | otherwise = current
    raiseAt j ts = [if k == j then t :~ High else t :~ l | (k, t :~ l) <- zip [0 ..] ts]
    setHigh j levels = [if k == j then High else l | (k, l) <- zip [0 ..] levels]

-- | Elaborate the module once, under the labels inference has chosen so far.
elaborateUnder :: Assembled -> Choices -> Either ElabError SomeModule
elaborateUnder assembled choices =
    case reflectCtx choices.chosenFunctionTypes assembled.globalTypes memTypes tableLimits (length m.dataSegments) of
        SomeModuleShape ctxS@(SModuleShape ftsS gsS msS tsS _) -> do
            functions <- gathered (elaborateFuncs ctxS assembled.sectionTypes assembled.declassify assembled.typingRestrictions ftsS entries)
            globals <- elaborateGlobals gsS (m.globals)
            dataSegments <- traverse (elaborateData (memsNonEmpty msS)) (zip [0 ..] m.dataSegments)
            elementSegments <- traverse (elaborateElements ftsS (tablesNonEmpty tsS)) (zip [0 ..] m.elementSegments)
            start <- traverse (resolveStart ftsS) (m.start)
            when (not (null assembled.secretRegions) && null m.memories) (Left (NoMemory "region"))
            Right (SomeModule ctxS (Module {functions, globals, dataSegments, secretRegions = assembled.secretRegions, elementSegments, exports = m.exports, start}))
  where
    m = assembled.annotated
    entries = zip3 [0 ..] assembled.loadDefaults (map Left m.imports ++ map (\(i, f) -> Right (f, Map.findWithDefault [] i choices.localLevels)) (zip [importCount ..] m.functions))
    -- A repairable failure raises what every function's failure names, not only the first's,
    -- which saves an elaboration per label; labels only rise, so this reaches the same labels.
    gathered :: Either ElabError a -> Either ElabError a
    gathered result = case result of
        Left (LevelTooLow raises failure) -> case reflectCtx choices.chosenFunctionTypes assembled.globalTypes memTypes tableLimits (length m.dataSegments) of
            SomeModuleShape ctxS@(SModuleShape ftsS _ _ _ _) ->
                Left (LevelTooLow (raises ++ concat [more | LevelTooLow more _ <- functionErrors ctxS assembled.sectionTypes assembled.declassify assembled.typingRestrictions ftsS entries]) failure)
        other -> other
    importCount = fromIntegral (length m.imports)
    tableLimits = [t.limits | t <- m.tables]
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
resolveStart :: Sing (fts :: [LabelledFuncType]) -> FunctionIdx -> Either ElabError (Elem ('LabelledFuncType 'Low '[] '[]) fts)
resolveStart ftsS (FunctionIdx idx) = do
    SomeFuncRef boundS psS rsS funcIx <- note (IndexOutOfRange Functions idx) (lookupFuncRef ftsS idx)
    Refl <- note InvalidStartFunction (decideEquality boundS SLow)
    Refl <- note InvalidStartFunction (decideEquality psS SNil)
    Refl <- note InvalidStartFunction (decideEquality rsS SNil)
    Right funcIx

{- | The functions, one per entry of the index space: an import is kept by name (linking is
  instantiation's job), a defined function is elaborated.
-}
elaborateFuncs ::
    SModuleShape shape ->
    [LabelledFuncType] ->
    Bool ->
    Restrictions ->
    Sing fts ->
    [(Word32, SecLevel, Either RawImport (RawFunction, [SecLevel]))] ->
    Either ElabError (FunctionSpace shape fts)
elaborateFuncs _ _ _ _ SNil [] = Right NoFunctions
elaborateFuncs ctxS types declassify restrictions (SCons ft fs) ((index, loadDefault, entry) : rest) = do
    fs' <- elaborateFuncs ctxS types declassify restrictions fs rest
    case entry of
        Left (RawImport moduleName fieldName (ImportFunc _)) -> Right (Imported moduleName fieldName fs')
        Right (f, localLevels) -> (`Defined` fs') <$> elaborateFunctionIn ctxS types loadDefault declassify restrictions index localLevels ft f
elaborateFuncs _ _ _ _ _ _ = Left (Malformed "function/signature count mismatch")

-- | The failure of every defined function that fails, each elaborated on its own.
functionErrors ::
    SModuleShape shape ->
    [LabelledFuncType] ->
    Bool ->
    Restrictions ->
    Sing (fts :: [LabelledFuncType]) ->
    [(Word32, SecLevel, Either RawImport (RawFunction, [SecLevel]))] ->
    [ElabError]
functionErrors ctxS types declassify restrictions (SCons ft fs) ((index, loadDefault, entry) : rest) =
    failure ++ functionErrors ctxS types declassify restrictions fs rest
  where
    failure = case entry of
        Right (f, localLevels) -> either pure (const []) (elaborateFunctionIn ctxS types loadDefault declassify restrictions index localLevels ft f)
        Left _ -> []
functionErrors _ _ _ _ _ _ = []

elaborateFunctionIn ::
    SModuleShape shape ->
    [LabelledFuncType] ->
    SecLevel ->
    Bool ->
    Restrictions ->
    Word32 ->
    [SecLevel] ->
    SLabelledFuncType ft ->
    RawFunction ->
    Either ElabError (Function shape ft)
elaborateFunctionIn ctxS types loadDefault declassify restrictions index localLevels (SLabelledFuncType boundS psS rsS) (RawFunction _ declaredT body) =
    case toSing (zipWith (:~) declaredT (localLevels ++ repeat Low)) of
        SomeSing declS ->
            let env = ElabEnv ctxS types rsS (sReverseOnto psS declS) (SCons rsS SNil) loadDefault declassify restrictions index 0 0
             in first (placeIn index) $ do
                    elaborated <- elabSeq env (SCons boundS SNil) SNil body
                    case elaborated of
                        Reachable _ _ soS bodySeq -> do
                            ended <- blame (raisesWhereBelow (RaiseResult index) rsS soS) (endAt "result" soS rsS bodySeq)
                            Right (Function psS declS ended)
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
elaborateElements :: Sing (fts :: [LabelledFuncType]) -> Maybe (NonEmptyTables ts) -> (Int, RawElementSegment) -> Either ElabError (ElementSegment fts)
elaborateElements ftsS tables (index, RawElementSegment offsetExpr functions) = do
    NonEmptyTables <- note (NoTable "elem") tables
    offset <- evalConstInit (InvalidElementSegmentOffset index) SI32 offsetExpr
    refs <- traverse (\(FunctionIdx f) -> note (IndexOutOfRange Functions f) (lookupFuncRef ftsS f)) functions
    Right (ElementSegment offset refs)
