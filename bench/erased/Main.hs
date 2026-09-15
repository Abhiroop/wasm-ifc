{- | The erased machine: the interpreter with its types forgotten (TODO.md §I, experiment E1).

  The question is whether intrinsic typing costs anything at run time. Racing some other
  untyped interpreter would compare algorithms as much as typing, so this is the typed machine
  itself with the types removed and nothing else changed:

  * The program is the one the elaborator produced, erased instruction by instruction
    ('eraseInstr'). An 'Elem' witness becomes a unary natural, so a local is still found by
    walking one step per position; an 'Append' width becomes one too. A numeric witness
    ('IsNum', 'IsInt', 'NumWithSign') becomes the plain value type its opcode names, and what a
    naive decoder knows from an opcode anyway — a conversion's two types, a narrow load's
    result type — is fixed once, at erasure.
  * Values carry their type as a tag, and every operation checks the tags of what it pops: the
    run-time check the typed machine never makes, because its configurations cannot be
    ill-typed. A failed check leaves the machine 'Stuck'.
  * The operand stack, locals and globals are strict cons lists, strict exactly where
    "Runtime.Stack"'s are; 'Config', 'Control' and 'Store' are strict where the typed ones are;
    and 'step', 'enterCall', 'popControl', 'unwind' and 'returnUnwind' mirror their typed
    counterparts clause for clause. The arithmetic is not reimplemented: it is the typed
    machine's own per-type helpers, chosen by tag instead of by witness.

  So the two machines differ in where a type comes from — a witness fixed at elaboration, or a
  tag read at run time — and in nothing else.

  > wasm-ifc-erased invoke <module.wasm> <export>

  Host calls are not supported: the kernels the experiment runs import nothing.
-}
module Main (main) where

import Data.Bifunctor (first)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as BL
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Kind (Type)
import Data.Maybe (fromMaybe)
import Data.Singletons.Base.TH (SList (SCons, SNil), Sing, fromSing)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Word (Word32, Word64)
import GHC.Exts (Any)
import System.Environment (getArgs)
import System.Exit (die)

import Codec.Wasm (decodeModule)
import Runtime.Convert (convertVal)
import Runtime.Instantiate (instantiate)
import Runtime.Interpreter (
    FuncInst (..),
    FuncSpaceInst (..),
    ModuleInst (..),
    bitwiseT,
    callDepthBound,
    countT,
    effectiveAddr,
    floatBinT,
    floatUnT,
    growFailed,
    loadValue,
    narrowLoadT,
    narrowStoreT,
    numBinary,
    numCompare,
    numDiv,
    numEqNe,
    numEqz,
    numRem,
    storedWord,
 )
import Runtime.MemInst (MemInst, copyWithin, fillBytes, growMemory, loadWord, memoryPages, storeWord, writeBytes)
import Runtime.Module (SomeModuleInst (..))
import Runtime.Stack (DataSpaceInst (..), GlobalSpaceInst (..), MemSpaceInst (..), TableSpaceInst (..))
import Runtime.TableInst (tableLookup, tableSize)
import Runtime.Trap (Trap (..))
import Syntax.Functions (Function (..))
import Syntax.Immediates (HostType, MemArg, NarrowWidth, NumWithSign (..), Signedness (..), narrowBytes, narrowInt)
import Syntax.Indices (FunctionIdx (..))
import Syntax.Instructions (BitwiseOp, ConvertOp, CountOp, Expr (..), FloatBinOp, FloatUnOp, Instr (..), convertEnds)
import Syntax.Module (Export (..), ExportDesc (..))
import Syntax.Types
import Validation.Elaborate (elaborateModule)
import Validation.Shape (Append (..), Elem (..), MemShape, SModuleShape (..), SomeFuncRef (..))

-- *** Values, indices, the erased program ***

-- | A value with its type as a tag.
data Value = VI32 !Word32 | VI64 !Word64 | VF32 !Float | VF64 !Double

-- | A cons list of values, strict in head and tail like 'Runtime.Stack.ValueStack'.
data Values = Empty | !Value :> !Values

infixr 5 :>

-- | What an 'Elem' or an 'Append' witness erases to: its length, in unary.
data Nat = Z | S !Nat

-- | A conversion, with the two types its opcode names.
data SomeConvert where
    SomeConvert :: !(IsNum from) -> !(IsNum to) -> !(ConvertOp from to) -> SomeConvert

-- | A narrow load or store, with the integer type its opcode names.
data SomeNarrow where
    SomeNarrow :: !(IsInt t) -> !(NarrowWidth t) -> SomeNarrow

data Instruction
    = EConst !Value
    | EAdd !ValType
    | ESub !ValType
    | EMul !ValType
    | EDiv !ValType !Signedness
    | ERem !ValType !Signedness
    | EEqz !ValType
    | EEq !ValType
    | ENe !ValType
    | ELt !ValType !Signedness
    | EGt !ValType !Signedness
    | ELe !ValType !Signedness
    | EGe !ValType !Signedness
    | EBitwise !ValType !BitwiseOp
    | ECount !ValType !CountOp
    | EFloatUn !ValType !FloatUnOp
    | EFloatBin !ValType !FloatBinOp
    | EConvert !SomeConvert
    | EMemSize
    | EMemGrow
    | ELoadN !SomeNarrow !Signedness !MemArg
    | EStoreN !SomeNarrow !MemArg
    | EMemCopy
    | EMemFill
    | EMemInit !Nat
    | EDataDrop !Nat
    | EDrop
    | ESelect
    | ELocalGet !Nat
    | ELocalSet !Nat
    | ELocalTee !Nat
    | EGlobalGet !Nat
    | EGlobalSet !Nat
    | ELoad !ValType !MemArg
    | EStore !ValType !MemArg
    | ECall !Nat !Nat
    | ECallIndirect !Nat !FuncType
    | EBlock !Nat [Instruction]
    | ELoop !Nat [Instruction]
    | EIf !Nat [Instruction] [Instruction]
    | EBr !Nat !Nat
    | EBrIf !Nat !Nat
    | EBrTable !Nat [Nat] !Nat
    | EReturn !Nat
    | ENop
    | EUnreachable

-- *** Runtime state, strict where the typed machine's is ***

data Func = WasmFunction ![ValType] [Instruction] | HostFunction

-- | The function index space; lazy, like 'FuncSpaceInst'.
data Funcs = NoFuncs | FuncCons Func Funcs

data FuncRef = FuncRef !FuncType !Nat

data Table = Table {size :: !Word32, entries :: !(IntMap FuncRef)}

data Segments = NoSegments | !(Maybe ByteString) :| !Segments

infixr 5 :|

type Store :: MemShape -> Type
data Store m = Store
    { globals :: !Values
    , memory :: !(Maybe (MemInst m))
    , table :: !(Maybe Table)
    , segments :: !Segments
    }

data Control
    = EntryBoundary
    | BlockLabel !Values [Instruction] Control
    | LoopLabel !Values [Instruction] [Instruction] Control
    | CallBoundary !Word !Values !Values [Instruction] Control

data Config m = Config !(Store m) !Values !Values [Instruction] Control

data StepResult m = Stepped !(Config m) | Done !(Store m) !Values | Wedged

-- | How a run fails: a WebAssembly trap, or a check the typed machine never has to make.
data Failure = Trapped Trap | Stuck | HostCallUnsupported

-- *** The step relation ***

step :: Funcs -> Config m -> Either Failure (StepResult m)
step funcs (Config store locals stack code control) = case code of
    [] -> Right (popControl store locals stack control)
    instr : rest -> case instr of
        {- Constants & numeric -}
        EConst v -> stepped store locals (v :> stack) rest control
        EAdd ty -> arithmetic store locals stack rest control ty (`numBinary` (+))
        ESub ty -> arithmetic store locals stack rest control ty (`numBinary` (-))
        EMul ty -> arithmetic store locals stack rest control ty (`numBinary` (*))
        EDiv ty sign -> case (ty, stack) of
            (I32, VI32 b :> VI32 a :> r) -> trapping store locals rest control VI32 (numDiv (i32WithSign sign) a b) r
            (I64, VI64 b :> VI64 a :> r) -> trapping store locals rest control VI64 (numDiv (i64WithSign sign) a b) r
            (F32, VF32 b :> VF32 a :> r) -> trapping store locals rest control VF32 (numDiv f32NoSign a b) r
            (F64, VF64 b :> VF64 a :> r) -> trapping store locals rest control VF64 (numDiv f64NoSign a b) r
            _ -> Left Stuck
        ERem ty sign -> case (ty, stack) of
            (I32, VI32 b :> VI32 a :> r) -> trapping store locals rest control VI32 (numRem I32IsInt sign a b) r
            (I64, VI64 b :> VI64 a :> r) -> trapping store locals rest control VI64 (numRem I64IsInt sign a b) r
            _ -> Left Stuck
        {- Comparison -}
        EEqz ty -> case (ty, stack) of
            (I32, VI32 a :> r) -> stepped store locals (VI32 (numEqz I32IsInt a) :> r) rest control
            (I64, VI64 a :> r) -> stepped store locals (VI32 (numEqz I64IsInt a) :> r) rest control
            _ -> Left Stuck
        EEq ty -> equality store locals stack rest control ty (numEqNe (==))
        ENe ty -> equality store locals stack rest control ty (numEqNe (/=))
        ELt ty sign -> ordering store locals stack rest control ty sign (numCompare (<))
        EGt ty sign -> ordering store locals stack rest control ty sign (numCompare (>))
        ELe ty sign -> ordering store locals stack rest control ty sign (numCompare (<=))
        EGe ty sign -> ordering store locals stack rest control ty sign (numCompare (>=))
        {- Conversions -}
        EConvert (SomeConvert from to op) -> case (from, stack) of
            (I32IsNum, VI32 x :> r) -> trapping store locals rest control (tagged to) (convertVal op x) r
            (I64IsNum, VI64 x :> r) -> trapping store locals rest control (tagged to) (convertVal op x) r
            (F32IsNum, VF32 x :> r) -> trapping store locals rest control (tagged to) (convertVal op x) r
            (F64IsNum, VF64 x :> r) -> trapping store locals rest control (tagged to) (convertVal op x) r
            _ -> Left Stuck
        {- Integer bitwise / shift / count, floating-point unary / binary -}
        EBitwise ty op -> case (ty, stack) of
            (I32, VI32 b :> VI32 a :> r) -> stepped store locals (VI32 (bitwiseT I32IsInt op a b) :> r) rest control
            (I64, VI64 b :> VI64 a :> r) -> stepped store locals (VI64 (bitwiseT I64IsInt op a b) :> r) rest control
            _ -> Left Stuck
        ECount ty op -> case (ty, stack) of
            (I32, VI32 a :> r) -> stepped store locals (VI32 (countT I32IsInt op a) :> r) rest control
            (I64, VI64 a :> r) -> stepped store locals (VI64 (countT I64IsInt op a) :> r) rest control
            _ -> Left Stuck
        EFloatUn ty op -> case (ty, stack) of
            (F32, VF32 a :> r) -> stepped store locals (VF32 (floatUnT F32IsFloat op a) :> r) rest control
            (F64, VF64 a :> r) -> stepped store locals (VF64 (floatUnT F64IsFloat op a) :> r) rest control
            _ -> Left Stuck
        EFloatBin ty op -> case (ty, stack) of
            (F32, VF32 b :> VF32 a :> r) -> stepped store locals (VF32 (floatBinT F32IsFloat op a b) :> r) rest control
            (F64, VF64 b :> VF64 a :> r) -> stepped store locals (VF64 (floatBinT F64IsFloat op a b) :> r) rest control
            _ -> Left Stuck
        {- Memory size / grow & narrow access -}
        EMemSize -> case store.memory of
            Just mem -> stepped store locals (VI32 (memoryPages mem) :> stack) rest control
            Nothing -> Left Stuck
        EMemGrow -> case (store.memory, stack) of
            (Just mem, VI32 delta :> r) -> case growMemory delta mem of
                Just grown -> stepped (withMemory grown store) locals (VI32 (memoryPages mem) :> r) rest control
                Nothing -> stepped store locals (VI32 growFailed :> r) rest control
            _ -> Left Stuck
        ELoadN (SomeNarrow it nw) sign memArg -> case (store.memory, stack) of
            (Just mem, VI32 addr :> r) -> case loadWord mem (effectiveAddr addr memArg) (narrowBytes nw) of
                Just word -> stepped store locals (taggedInt it (narrowLoadT nw sign word) :> r) rest control
                Nothing -> Left (Trapped OutOfBoundsMemoryAccess)
            _ -> Left Stuck
        EStoreN (SomeNarrow it nw) memArg -> case (store.memory, it, stack) of
            (Just mem, I32IsInt, VI32 value :> VI32 addr :> r) ->
                written store locals rest control (storeWord mem (effectiveAddr addr memArg) (narrowBytes nw) (narrowStoreT nw value)) r
            (Just mem, I64IsInt, VI64 value :> VI32 addr :> r) ->
                written store locals rest control (storeWord mem (effectiveAddr addr memArg) (narrowBytes nw) (narrowStoreT nw value)) r
            _ -> Left Stuck
        {- Bulk memory: each checks both ranges before writing anything -}
        EMemCopy -> case (store.memory, stack) of
            (Just mem, VI32 count :> VI32 src :> VI32 dst :> r) ->
                written store locals rest control (copyWithin (fromIntegral dst) (fromIntegral src) (fromIntegral count) mem) r
            _ -> Left Stuck
        EMemFill -> case (store.memory, stack) of
            (Just mem, VI32 count :> VI32 value :> VI32 dst :> r) ->
                written store locals rest control (fillBytes (fromIntegral dst) (fromIntegral value) (fromIntegral count) mem) r
            _ -> Left Stuck
        EMemInit segmentIx -> case (store.memory, stack) of
            (Just mem, VI32 count :> VI32 srcOffset :> VI32 dst :> r) ->
                let segment = fromMaybe BS.empty (segmentAt segmentIx store.segments)
                    n = fromIntegral count
                    src = fromIntegral srcOffset
                    inSegment = src + n <= BS.length segment
                    bytes = writeBytes mem (fromIntegral dst) (BS.unpack (BS.take n (BS.drop src segment)))
                 in case (inSegment, bytes) of
                        (True, Just mem') -> stepped (withMemory mem' store) locals r rest control
                        _ -> Left (Trapped OutOfBoundsMemoryAccess)
            _ -> Left Stuck
        EDataDrop segmentIx -> stepped (withSegments (dropSegmentAt segmentIx store.segments) store) locals stack rest control
        {- Stack management -}
        EDrop -> case stack of
            _ :> r -> stepped store locals r rest control
            Empty -> Left Stuck
        ESelect -> case stack of
            VI32 cond :> second :> first' :> r ->
                stepped store locals ((if cond /= 0 then first' else second) :> r) rest control
            _ -> Left Stuck
        {- Locals & globals -}
        ELocalGet ix -> stepped store locals (valueAt ix locals :> stack) rest control
        ELocalSet ix -> case stack of
            v :> r -> stepped store (replaceAt ix v locals) r rest control
            Empty -> Left Stuck
        ELocalTee ix -> case stack of
            v :> _ -> stepped store (replaceAt ix v locals) stack rest control
            Empty -> Left Stuck
        EGlobalGet ix -> stepped store locals (valueAt ix store.globals :> stack) rest control
        EGlobalSet ix -> case stack of
            v :> r -> stepped (withGlobals (replaceAt ix v store.globals) store) locals r rest control
            Empty -> Left Stuck
        {- Memory -}
        ELoad ty memArg -> case (store.memory, stack) of
            (Just mem, VI32 addr :> r) -> case loadWord mem (effectiveAddr addr memArg) (byteWidth ty) of
                Just word -> stepped store locals (loaded ty word :> r) rest control
                Nothing -> Left (Trapped OutOfBoundsMemoryAccess)
            _ -> Left Stuck
        EStore ty memArg -> case (store.memory, ty, stack) of
            (Just mem, I32, VI32 v :> VI32 addr :> r) -> written store locals rest control (storeWord mem (effectiveAddr addr memArg) (numBytes I32IsNum) (storedWord I32IsNum v)) r
            (Just mem, I64, VI64 v :> VI32 addr :> r) -> written store locals rest control (storeWord mem (effectiveAddr addr memArg) (numBytes I64IsNum) (storedWord I64IsNum v)) r
            (Just mem, F32, VF32 v :> VI32 addr :> r) -> written store locals rest control (storeWord mem (effectiveAddr addr memArg) (numBytes F32IsNum) (storedWord F32IsNum v)) r
            (Just mem, F64, VF64 v :> VI32 addr :> r) -> written store locals rest control (storeWord mem (effectiveAddr addr memArg) (numBytes F64IsNum) (storedWord F64IsNum v)) r
            _ -> Left Stuck
        {- Calls: an indirect call first reads the table entry and compares its type -}
        ECall width ix -> enterCall funcs store locals width ix stack rest control
        ECallIndirect width expected -> case stack of
            VI32 index :> below' -> case lookupTable store.table index of
                Left failure -> Left failure
                Right (FuncRef actual ix)
                    | actual == expected -> enterCall funcs store locals width ix below' rest control
                    | otherwise -> Left (Trapped IndirectCallTypeMismatch)
            _ -> Left Stuck
        {- Structured control: push the matching frame and run the body -}
        EBlock width body ->
            let (params, below) = splitValues width stack
             in Right (Stepped (Config store locals params body (BlockLabel below rest control)))
        ELoop width body ->
            let (params, below) = splitValues width stack
             in Right (Stepped (Config store locals params body (LoopLabel below body rest control)))
        EIf width thenArm elseArm -> case stack of
            VI32 cond :> below' ->
                let (params, below) = splitValues width below'
                    arm = if cond /= 0 then thenArm else elseArm
                 in Right (Stepped (Config store locals params arm (BlockLabel below rest control)))
            _ -> Left Stuck
        {- Branches: unwind the control stack to the targeted frame -}
        EBr width ix -> let (vs, _) = splitValues width stack in Right (unwind store locals ix vs control)
        EBrIf width ix -> case stack of
            VI32 cond :> below'
                | cond /= 0 ->
                    let (vs, _) = splitValues width below'
                     in Right (unwind store locals ix vs control)
                | otherwise -> stepped store locals below' rest control
            _ -> Left Stuck
        EBrTable width targets def -> case stack of
            VI32 idx :> below' ->
                let target = case drop (fromIntegral idx) targets of t : _ -> t; [] -> def
                    (vs, _) = splitValues width below'
                 in Right (unwind store locals target vs control)
            _ -> Left Stuck
        EReturn width -> let (vs, _) = splitValues width stack in Right (returnUnwind store locals vs control)
        {- Inert -}
        ENop -> stepped store locals stack rest control
        EUnreachable -> Left (Trapped UnreachableExecuted)

enterCall :: Funcs -> Store m -> Values -> Nat -> Nat -> Values -> [Instruction] -> Control -> Either Failure (StepResult m)
enterCall funcs store locals width ix stack rest control = case functionAt ix funcs of
    WasmFunction declared body
        | depth > callDepthBound -> Left (Trapped CallStackExhausted)
        | otherwise ->
            let (args, below) = splitValues width stack
                calleeLocals = reverseOnto args (defaultLocals declared)
             in Right (Stepped (Config store calleeLocals Empty body (CallBoundary depth below locals rest control)))
    HostFunction -> Left HostCallUnsupported
  where
    depth = activationDepth control + 1

activationDepth :: Control -> Word
activationDepth control = case control of
    EntryBoundary -> 1
    CallBoundary depth _ _ _ _ -> depth
    BlockLabel _ _ rest -> activationDepth rest
    LoopLabel _ _ _ rest -> activationDepth rest

stepped :: Store m -> Values -> Values -> [Instruction] -> Control -> Either Failure (StepResult m)
stepped store locals stack code control = Right (Stepped (Config store locals stack code control))

{- | Push a result that may have trapped, tagging it on the way (no intermediate 'Either' is
  built: the typed machine cases on the helper's result directly, and so does this).
-}
trapping :: Store m -> Values -> [Instruction] -> Control -> (a -> Value) -> Either Trap a -> Values -> Either Failure (StepResult m)
trapping store locals rest control tag result r = case result of
    Right v -> stepped store locals (tag v :> r) rest control
    Left t -> Left (Trapped t)

-- | Continue with a memory a write produced, or trap if it was out of bounds.
written :: Store m -> Values -> [Instruction] -> Control -> Maybe (MemInst m) -> Values -> Either Failure (StepResult m)
written store locals rest control result r = case result of
    Just mem' -> stepped (withMemory mem' store) locals r rest control
    Nothing -> Left (Trapped OutOfBoundsMemoryAccess)

type Arithmetic = forall t. IsNum t -> HostType t -> HostType t -> HostType t

arithmetic :: Store m -> Values -> Values -> [Instruction] -> Control -> ValType -> Arithmetic -> Either Failure (StepResult m)
arithmetic store locals stack rest control ty op = case (ty, stack) of
    (I32, VI32 b :> VI32 a :> r) -> stepped store locals (VI32 (op I32IsNum a b) :> r) rest control
    (I64, VI64 b :> VI64 a :> r) -> stepped store locals (VI64 (op I64IsNum a b) :> r) rest control
    (F32, VF32 b :> VF32 a :> r) -> stepped store locals (VF32 (op F32IsNum a b) :> r) rest control
    (F64, VF64 b :> VF64 a :> r) -> stepped store locals (VF64 (op F64IsNum a b) :> r) rest control
    _ -> Left Stuck

type Equality = forall t. IsNum t -> HostType t -> HostType t -> Word32

equality :: Store m -> Values -> Values -> [Instruction] -> Control -> ValType -> Equality -> Either Failure (StepResult m)
equality store locals stack rest control ty op = case (ty, stack) of
    (I32, VI32 b :> VI32 a :> r) -> stepped store locals (VI32 (op I32IsNum a b) :> r) rest control
    (I64, VI64 b :> VI64 a :> r) -> stepped store locals (VI32 (op I64IsNum a b) :> r) rest control
    (F32, VF32 b :> VF32 a :> r) -> stepped store locals (VI32 (op F32IsNum a b) :> r) rest control
    (F64, VF64 b :> VF64 a :> r) -> stepped store locals (VI32 (op F64IsNum a b) :> r) rest control
    _ -> Left Stuck

type Ordering' = forall t. NumWithSign t -> HostType t -> HostType t -> Word32

ordering :: Store m -> Values -> Values -> [Instruction] -> Control -> ValType -> Signedness -> Ordering' -> Either Failure (StepResult m)
ordering store locals stack rest control ty sign op = case (ty, stack) of
    (I32, VI32 b :> VI32 a :> r) -> stepped store locals (VI32 (op (i32WithSign sign) a b) :> r) rest control
    (I64, VI64 b :> VI64 a :> r) -> stepped store locals (VI32 (op (i64WithSign sign) a b) :> r) rest control
    (F32, VF32 b :> VF32 a :> r) -> stepped store locals (VI32 (op f32NoSign a b) :> r) rest control
    (F64, VF64 b :> VF64 a :> r) -> stepped store locals (VI32 (op f64NoSign a b) :> r) rest control
    _ -> Left Stuck

-- The signed-comparison witnesses, built once rather than per step (the typed instruction
-- carries its witness prebuilt, so building one per step would not be a fair erasure).
i32WithSign :: Signedness -> NumWithSign 'I32
i32WithSign Signed = i32Signed
i32WithSign Unsigned = i32Unsigned

i64WithSign :: Signedness -> NumWithSign 'I64
i64WithSign Signed = i64Signed
i64WithSign Unsigned = i64Unsigned

i32Signed, i32Unsigned :: NumWithSign 'I32
i32Signed = IntsHaveSign I32IsInt Signed
i32Unsigned = IntsHaveSign I32IsInt Unsigned

i64Signed, i64Unsigned :: NumWithSign 'I64
i64Signed = IntsHaveSign I64IsInt Signed
i64Unsigned = IntsHaveSign I64IsInt Unsigned

f32NoSign :: NumWithSign 'F32
f32NoSign = FloatsHaveNoSign F32IsFloat

f64NoSign :: NumWithSign 'F64
f64NoSign = FloatsHaveNoSign F64IsFloat

tagged :: IsNum t -> HostType t -> Value
tagged I32IsNum = VI32
tagged I64IsNum = VI64
tagged F32IsNum = VF32
tagged F64IsNum = VF64

taggedInt :: IsInt t -> HostType t -> Value
taggedInt I32IsInt = VI32
taggedInt I64IsInt = VI64

byteWidth :: ValType -> Int
byteWidth ty = case ty of I32 -> 4; I64 -> 8; F32 -> 4; F64 -> 8

loaded :: ValType -> Word64 -> Value
loaded I32 word = VI32 (loadValue I32IsNum word)
loaded I64 word = VI64 (loadValue I64IsNum word)
loaded F32 word = VF32 (loadValue F32IsNum word)
loaded F64 word = VF64 (loadValue F64IsNum word)

withMemory :: MemInst m -> Store m -> Store m
withMemory mem store = Store {globals = store.globals, memory = Just mem, table = store.table, segments = store.segments}

withGlobals :: Values -> Store m -> Store m
withGlobals gs store = Store {globals = gs, memory = store.memory, table = store.table, segments = store.segments}

withSegments :: Segments -> Store m -> Store m
withSegments segs store = Store {globals = store.globals, memory = store.memory, table = store.table, segments = segs}

lookupTable :: Maybe Table -> Word32 -> Either Failure FuncRef
lookupTable Nothing _ = Left Stuck
lookupTable (Just t) index
    | index >= t.size = Left (Trapped UndefinedElement)
    | otherwise = maybe (Left (Trapped UninitializedElement)) Right (IntMap.lookup (fromIntegral index) t.entries)

-- *** Lists by unary index: the erasure of 'getLocal', 'setLocal', 'getFunc', ... ***

-- An index past the end cannot come from a validated program; the typed machine has no such
-- case at all, and these return something harmless rather than add a check the typed
-- functions do not make. The kernels' checksums catch any mistake here.
valueAt :: Nat -> Values -> Value
valueAt Z (x :> _) = x
valueAt (S ix) (_ :> rest) = valueAt ix rest
valueAt _ Empty = VI32 0

replaceAt :: Nat -> Value -> Values -> Values
replaceAt Z v (_ :> rest) = v :> rest
replaceAt (S ix) v (x :> rest) = x :> replaceAt ix v rest
replaceAt _ _ Empty = Empty

functionAt :: Nat -> Funcs -> Func
functionAt Z (FuncCons f _) = f
functionAt (S ix) (FuncCons _ rest) = functionAt ix rest
functionAt _ NoFuncs = HostFunction

segmentAt :: Nat -> Segments -> Maybe ByteString
segmentAt Z (s :| _) = s
segmentAt (S ix) (_ :| rest) = segmentAt ix rest
segmentAt _ NoSegments = Nothing

dropSegmentAt :: Nat -> Segments -> Segments
dropSegmentAt Z (_ :| rest) = Nothing :| rest
dropSegmentAt (S ix) (s :| rest) = s :| dropSegmentAt ix rest
dropSegmentAt _ NoSegments = NoSegments

appendValues :: Values -> Values -> Values
appendValues Empty ys = ys
appendValues (x :> xs) ys = x :> appendValues xs ys

splitValues :: Nat -> Values -> (Values, Values)
splitValues Z vs = (Empty, vs)
splitValues (S w) (x :> vs) = let (upper, lower) = splitValues w vs in (x :> upper, lower)
splitValues (S _) Empty = (Empty, Empty)

reverseOnto :: Values -> Values -> Values
reverseOnto Empty acc = acc
reverseOnto (x :> xs) acc = reverseOnto xs (x :> acc)

defaultLocals :: [ValType] -> Values
defaultLocals [] = Empty
defaultLocals (ty : rest) = zeroOf ty :> defaultLocals rest
  where
    zeroOf I32 = VI32 0
    zeroOf I64 = VI64 0
    zeroOf F32 = VF32 0
    zeroOf F64 = VF64 0

-- *** Leaving frames ***

resume :: Store m -> Values -> Values -> Values -> [Instruction] -> Control -> StepResult m
resume store locals vs below cont rest = Stepped (Config store locals (appendValues vs below) cont rest)

popControl :: Store m -> Values -> Values -> Control -> StepResult m
popControl store _ vs EntryBoundary = Done store vs
popControl store locals vs (BlockLabel below cont rest) = resume store locals vs below cont rest
popControl store locals vs (LoopLabel below _ cont rest) = resume store locals vs below cont rest
popControl store _ vs (CallBoundary _ below cl cont cf) = resume store cl vs below cont cf

unwind :: Store m -> Values -> Nat -> Values -> Control -> StepResult m
unwind store _ Z vs EntryBoundary = Done store vs
unwind store locals Z vs (BlockLabel below cont rest) = resume store locals vs below cont rest
unwind store locals Z vs (LoopLabel below body cont rest) =
    Stepped (Config store locals vs body (LoopLabel below body cont rest))
unwind store _ Z vs (CallBoundary _ below cl cont cf) = resume store cl vs below cont cf
unwind store locals (S ix') vs (BlockLabel _ _ rest) = unwind store locals ix' vs rest
unwind store locals (S ix') vs (LoopLabel _ _ _ rest) = unwind store locals ix' vs rest
unwind _ _ (S _) _ (CallBoundary {}) = Wedged
unwind _ _ (S _) _ EntryBoundary = Wedged

returnUnwind :: Store m -> Values -> Values -> Control -> StepResult m
returnUnwind store _ vs EntryBoundary = Done store vs
returnUnwind store _ vs (CallBoundary _ below cl cont cf) = resume store cl vs below cont cf
returnUnwind store locals vs (BlockLabel _ _ rest) = returnUnwind store locals vs rest
returnUnwind store locals vs (LoopLabel _ _ _ rest) = returnUnwind store locals vs rest

run :: Funcs -> Config m -> Either Failure Values
run funcs config = case step funcs config of
    Left failure -> Left failure
    Right (Done _ vs) -> Right vs
    Right Wedged -> Left Stuck
    Right (Stepped next) -> run funcs next

-- *** Erasure ***

eraseExpr :: Expr m f l s o -> [Instruction]
eraseExpr INil = []
eraseExpr (instr :. rest) = eraseInstr instr : eraseExpr rest

eraseInstr :: Instr m f l s o -> Instruction
eraseInstr instr = case instr of
    IConst nt v -> EConst (tagged nt v)
    IAdd nt -> EAdd (numType nt)
    ISub nt -> ESub (numType nt)
    IMul nt -> EMul (numType nt)
    IDiv sn -> uncurry EDiv (signedType sn)
    IRem it sign -> ERem (intType it) sign
    IEqz it -> EEqz (intType it)
    IEq nt -> EEq (numType nt)
    INe nt -> ENe (numType nt)
    ILt sn -> uncurry ELt (signedType sn)
    IGt sn -> uncurry EGt (signedType sn)
    ILe sn -> uncurry ELe (signedType sn)
    IGe sn -> uncurry EGe (signedType sn)
    IBitwise it op -> EBitwise (intType it) op
    ICount it op -> ECount (intType it) op
    IFloatUn ft op -> EFloatUn (floatType ft) op
    IFloatBin ft op -> EFloatBin (floatType ft) op
    IConvert op -> let (from, to) = convertEnds op in EConvert (SomeConvert from to op)
    IMemSize -> EMemSize
    IMemGrow -> EMemGrow
    ILoadN nw sign memArg -> ELoadN (SomeNarrow (narrowInt nw) nw) sign memArg
    IStoreN nw memArg -> EStoreN (SomeNarrow (narrowInt nw) nw) memArg
    IMemCopy -> EMemCopy
    IMemFill -> EMemFill
    IMemInit ix -> EMemInit (positionOf ix)
    IDataDrop ix -> EDataDrop (positionOf ix)
    IDrop -> EDrop
    ISelect _ -> ESelect
    ILocalGet ix -> ELocalGet (positionOf ix)
    ILocalSet ix -> ELocalSet (positionOf ix)
    ILocalTee ix -> ELocalTee (positionOf ix)
    IGlobalGet ix -> EGlobalGet (positionOf ix)
    IGlobalSet ix -> EGlobalSet (positionOf ix)
    ILoad nt memArg -> ELoad (numType nt) memArg
    IStore nt memArg -> EStore (numType nt) memArg
    ICall witness ix -> ECall (widthOf witness) (positionOf ix)
    ICallIndirect witness (SFuncType params results) -> ECallIndirect (widthOf witness) (FuncType (fromSing params) (fromSing results))
    IBlock witness body -> EBlock (widthOf witness) (eraseExpr body)
    ILoop witness body -> ELoop (widthOf witness) (eraseExpr body)
    IIf witness thenArm elseArm -> EIf (widthOf witness) (eraseExpr thenArm) (eraseExpr elseArm)
    IBr witness ix -> EBr (widthOf witness) (positionOf ix)
    IBrIf witness ix -> EBrIf (widthOf witness) (positionOf ix)
    IBrTable witness targets def -> EBrTable (widthOf witness) (map positionOf targets) (positionOf def)
    IReturn witness -> EReturn (widthOf witness)
    INop -> ENop
    IUnreachable -> EUnreachable

positionOf :: Elem x xs -> Nat
positionOf Here = Z
positionOf (There ix) = S (positionOf ix)

widthOf :: Append a b c -> Nat
widthOf ANil = Z
widthOf (ACons w) = S (widthOf w)

numType :: IsNum t -> ValType
numType nt = case nt of I32IsNum -> I32; I64IsNum -> I64; F32IsNum -> F32; F64IsNum -> F64

intType :: IsInt t -> ValType
intType it = case it of I32IsInt -> I32; I64IsInt -> I64

floatType :: IsFloat t -> ValType
floatType ft = case ft of F32IsFloat -> F32; F64IsFloat -> F64

signedType :: NumWithSign t -> (ValType, Signedness)
signedType (IntsHaveSign it sign) = (intType it, sign)
signedType (FloatsHaveNoSign ft) = (floatType ft, Signed)

eraseFunctions :: FuncSpaceInst mod fts -> Funcs
eraseFunctions FsNil = NoFuncs
eraseFunctions (FsCons (WasmFunc (Function declared body)) rest) = FuncCons (WasmFunction (fromSing declared) (eraseExpr body)) (eraseFunctions rest)
eraseFunctions (FsCons (HostFunc _) rest) = FuncCons HostFunction (eraseFunctions rest)

eraseGlobals :: Sing (gs :: [GlobalType]) -> GlobalSpaceInst gs -> Values
eraseGlobals SNil GNil = Empty
eraseGlobals (SCons (SGlobalType _ valTypeS) rest) (GCons v vs) = valueOf valTypeS v :> eraseGlobals rest vs
  where
    valueOf :: Sing (t :: ValType) -> HostType t -> Value
    valueOf SI32 = VI32
    valueOf SI64 = VI64
    valueOf SF32 = VF32
    valueOf SF64 = VF64

eraseTable :: TableSpaceInst fts ts -> Maybe Table
eraseTable TNil = Nothing
eraseTable (TCons t _) = Just (Table n (IntMap.fromList [(fromIntegral i, erased ref) | n > 0, i <- [0 .. n - 1], Right ref <- [tableLookup t i]]))
  where
    n = tableSize t
    erased (SomeFuncRef params results ix) = FuncRef (FuncType (fromSing params) (fromSing results)) (positionOf ix)

eraseSegments :: DataSpaceInst ds -> Segments
eraseSegments DNil = NoSegments
eraseSegments (DCons s rest) = s :| eraseSegments rest

data SomeStore where
    SomeStore :: Store m -> SomeStore

-- | Walk every function body once, so the run starts from a fully built program.
forced :: Funcs -> Funcs
forced funcs = go funcs `seq` funcs
  where
    go NoFuncs = ()
    go (FuncCons (WasmFunction declared body) rest) = length declared `seq` body' body `seq` go rest
    go (FuncCons HostFunction rest) = go rest
    body' = foldr (\i acc -> instruction i `seq` acc) ()
    instruction i = case i of
        EBlock _ b -> body' b
        ELoop _ b -> body' b
        EIf _ t e -> body' t `seq` body' e
        EBrTable _ ts _ -> length ts `seq` ()
        _ -> ()

runExport :: SomeModuleInst -> Text -> Either String [Value]
runExport (SomeModuleInst (SModuleShape _ globalTypesS _ _ _) inst exports) name =
    case [index | Export exportName (ExportFunc (FunctionIdx index)) <- exports, exportName == name] of
        [] -> Left ("no exported function named " ++ T.unpack name)
        index : _ -> case functionAt (unary index) funcs of
            HostFunction -> Left "the erased machine does not serve host calls"
            WasmFunction declared body -> case someStore of
                SomeStore store -> case run funcs (Config store (reverseOnto Empty (defaultLocals declared)) Empty body EntryBoundary) of
                    Right results -> Right (toList results)
                    Left (Trapped trap) -> Left ("trap: " ++ show trap)
                    Left Stuck -> Left "stuck: the machine reached an ill-typed configuration"
                    Left HostCallUnsupported -> Left "the erased machine does not serve host calls"
  where
    funcs = forced (eraseFunctions inst.functions)
    globalValues = eraseGlobals globalTypesS inst.globals
    someStore = case inst.memories of
        MCons mem _ -> SomeStore (Store globalValues (Just mem) (eraseTable inst.tables) (eraseSegments inst.dataSegments))
        MNil -> SomeStore (Store globalValues Nothing (eraseTable inst.tables) (eraseSegments inst.dataSegments) :: Store Any)
    unary :: Word32 -> Nat
    unary 0 = Z
    unary k = S (unary (k - 1))
    toList Empty = []
    toList (v :> vs) = v : toList vs

render :: Value -> String
render v = case v of
    VI32 w -> show w
    VI64 w -> show w
    VF32 f -> show f
    VF64 d -> show d

main :: IO ()
main = do
    args <- getArgs
    case args of
        ["invoke", path, name] -> do
            bytes <- BL.readFile path
            either die (mapM_ (putStrLn . render)) $ do
                raw <- first ("Decode error: " ++) (decodeModule bytes)
                validated <- first (("Validation error: " ++) . show) (elaborateModule raw)
                instantiated <- first (("Instantiation error: " ++) . show) (instantiate validated)
                runExport instantiated (T.pack name)
        _ -> die "usage: wasm-ifc-erased invoke <module.wasm> <export>"
