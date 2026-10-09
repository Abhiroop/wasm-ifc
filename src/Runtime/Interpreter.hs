{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
-- -O2 for this module alone: its specialisation passes (SpecConstr above all) are what stop the
-- driver loop building a Config and a Stepped for every step, which at -O1 it did even with
-- 'step' inlined. With them the typed machine allocates less than its erased twin, where at -O1
-- it allocated twice as much (TODO.md §I, E1/E6). Confined to this module because it is the one
-- that runs hot, and -O2 costs compile time wherever it is on.
--
-- -fno-spec-constr-count lifts SpecConstr's limit of three specialisations per function. The
-- driver's continuation is specialised once per shape of "stepped to this configuration". With
-- security levels in the stack types those shapes differ in more type variables, there are
-- more than three of them, and under the default limit most instructions fell back to building
-- the Stepped and the Config after all: 60 bytes more per step, which bench/tripwire.py caught
-- when the levels went in (2026-09-20). Without the limit the figures equal the unlabelled
-- build's exactly.
{-# OPTIONS_GHC -O2 -fno-spec-constr-count #-}

{- | The intrinsically-typed interpreter, as a small-step abstract machine.

A 'Config' is a machine configuration: the mutable store, the active frame's locals, the
current value stack, the instruction sequence left to run, and a 'Control' stack of what
to do when the current sequence finishes or a branch unwinds to it. 'step'
advances one configuration; 'run' iterates it.

The point of this shape (rather than a recursive big-step evaluator) is that it /is/ the
type-soundness argument:

  * Preservation is by construction — 'Config' and 'Control' are indexed so only
    well-typed configurations are representable, and 'step' produces another 'Config'.
  * Progress is the totality of 'step' — it is defined on every non-final configuration,
    with no @error@ and no incomplete pattern (the index of each instruction guarantees
    the operands it needs are present, and the GADTs make every dispatch exhaustive).
  * A 'Trap' is a defined result, not a stuck state: 'step' may return @Left trap@ for the
    spec-defined runtime errors (division by zero, out-of-bounds access, @unreachable@,
    call-stack exhaustion).

So progress reads: every well-typed configuration either steps, finishes, or traps.
-}
module Runtime.Interpreter (
    FuncInst (..),
    FuncSpaceInst (..),
    getFunc,
    ModuleInst (..),
    Store (..),
    moduleToStore,
    storeToModule,
    currentMem,
    storeMem,
    Config (..),
    Control (..),
    StepResult (..),
    SomeStepResult (..),
    HostRequest (..),
    Suspended (..),
    resumeWith,
    Halt (..),
    Fuelled (..),
    runFor,
    Outcome (..),
    step,
    stepInstr,
    run,
    runFunction,
    callDepthBound,

    -- * Per-type operations

    {- | Exported for the benchmarks' erased machine (@bench/erased@), which picks these by a
    value's tag where 'step' picks them by a witness, so that the two machines differ only in
    where a type comes from.
    -}
    numBinary,
    numDiv,
    numRem,
    numCompare,
    numEqNe,
    numEqz,
    bitwiseT,
    countT,
    floatUnT,
    floatBinT,
    loadValue,
    storedWord,
    narrowLoadT,
    narrowStoreT,
    effectiveAddr,
    growFailed,
) where

import Data.Bits (
    FiniteBits,
    complement,
    countLeadingZeros,
    countTrailingZeros,
    popCount,
    rotateL,
    rotateR,
    shiftL,
    shiftR,
    testBit,
    xor,
    (.&.),
    (.|.),
 )
import Data.Text (Text)
import Data.Word (Word32, Word64)
import GHC.Float (castDoubleToWord64, castFloatToWord32, castWord32ToFloat, castWord64ToDouble)

import Data.ByteString qualified as BS
import Data.List.Singletons (type (++))
import Data.Maybe (fromMaybe)
import Data.Singletons (Sing, fromSing)
import Data.Type.Equality ((:~:) (Refl))
import Runtime.Convert (convertVal)
import Runtime.Host (WasiFunc)
import Runtime.MemInst (LoadFailure (..), MemInst, checkedWord, copyWithinAt, fillBytesAt, growMemory, loadChecked, memoryPages, storeWordAt, writeBytesAt)
import Runtime.Numeric (copysign32, copysign64, fromSigned32, fromSigned64, intDiv32, intDiv64, intRem32, intRem64, toSigned32, toSigned64, wasmMax, wasmMin)
import Runtime.Obligation (CheckPassed (..))
import Runtime.Stack
import Runtime.TableInst (TableInst, enteredCallee, fillEntries, getEntry, growTable, lookupChecked, readEntries, setEntry, tableSize, writeEntries)
import Runtime.Trap (Trap (..))
import Syntax.Functions (Function (..))
import Syntax.Immediates
import Syntax.Instructions (
    BitwiseOp (..),
    CountOp (..),
    Expr (..),
    FallThrough (..),
    FloatBinOp (..),
    FloatUnOp (..),
    Instr (..),
 )
import Syntax.Types
import Syntax.TypesIFC
import Validation.Ref (functionReference)
import Validation.Reflect (appendNil)
import Validation.Shape (Append (..), BranchTarget (..), DataShape (..), Elem (..), ElemShape (..), FrameShape (..), ModuleData, ModuleElems, ModuleFuncs, ModuleGlobals, ModuleMems, ModuleShape, ModuleTables, PreservedOf, Restores (..), ReturnsWith (..), appendFromSing, appendIs, withinReach)

-- *** Module and runtime state ***

{- | A function instance: a validated WebAssembly 'Function', or the host function an import
  was linked to. A host function can only live in a module that has a memory, which WASI
  requires; the constraint is packed here so the driver can reach that memory without asking.
-}
data FuncInst (mod :: ModuleShape) (ft :: LabelledFuncType) where
    WasmFunc :: Function mod ft -> FuncInst mod ft
    {- | An import from the @ifc@ module: an annotation in the shape of a function
    ("Validation.Policy"). Assembly rewrote every call to it and refused to export it, start
    it or put it in a table, so it is never entered; it still has to occupy its place in the
    index space, and entering it is the one defined outcome left, a trap.
    -}
    GhostFunc :: FuncInst mod ft
    {- | A host function, which the module imports at a type its policy labels while the host's
    own type is public throughout. The host is called only from a public context (the import's
    bound is 'Low) and only with public arguments (they flow into the host's public
    parameters), since a host function's effects are observable; its results may be declared
    at any level, and the boundary retags the words on the way back.
    -}
    HostFunc ::
        (ModuleMems mod ~ (mem ': mems)) =>
        WasiFunc ('LabelledFuncType 'Low hostParams hostResults) ->
        SegmentFlows ps hostParams ->
        SameValueTypes hostResults rs ->
        FuncInst mod ('LabelledFuncType 'Low ps rs)
    {- | A function of whoever embeds the module, known by the names it is imported under: a
    function of another module, in a script that links several. Like a host function it is
    called from a public context with public arguments only, since what it does with them is
    outside this module's policy; its results have the levels the policy declares. A call to
    it suspends the machine ('ForeignRequest'), and the embedder answers with the results.
    -}
    ForeignFunc ::
        Text ->
        Text ->
        Sing ps ->
        Sing rs ->
        AllPublic ps ->
        FuncInst mod ('LabelledFuncType 'Low ps rs)

-- | The instance of a module's function index space: one 'FuncInst' per type in 'ModuleFuncs'.
data FuncSpaceInst (mod :: ModuleShape) (fts :: [LabelledFuncType]) where
    FsNil :: FuncSpaceInst mod '[]
    FsCons :: FuncInst mod ft -> FuncSpaceInst mod fts -> FuncSpaceInst mod (ft ': fts)

getFunc :: Elem ft fts -> FuncSpaceInst mod fts -> FuncInst mod ft
getFunc Here (FsCons f _) = f
getFunc (There ix) (FsCons _ rest) = getFunc ix rest

{- | The mutable part of the running state: the globals and memories that instructions update
  in place, and the tables @call_indirect@ reads. (Functions are immutable, so they are passed
  to 'step' read-only rather than kept here.)
-}
data Store (mod :: ModuleShape) = Store
    { globals :: !(GlobalSpaceInst (ModuleGlobals mod))
    , memories :: !(MemSpaceInst (ModuleMems mod))
    , tables :: !(TableSpaceInst (ModuleFuncs mod) (ModuleTables mod) (ModuleElems mod))
    , dataSegments :: !(DataSpaceInst (ModuleData mod))
    }

{- | A fully instantiated module: the instances of its function, global, memory, table and
  data index spaces. (The runtime counterpart of a validated 'Syntax.Module.Module', per the
  syntax/shape/instance naming: @Module@ → 'Validation.Shape.ModuleShape' → 'ModuleInst'.)
-}
data ModuleInst (mod :: ModuleShape) = ModuleInst
    { functions :: !(FuncSpaceInst mod (ModuleFuncs mod))
    , globals :: !(GlobalSpaceInst (ModuleGlobals mod))
    , memories :: !(MemSpaceInst (ModuleMems mod))
    , tables :: !(TableSpaceInst (ModuleFuncs mod) (ModuleTables mod) (ModuleElems mod))
    , dataSegments :: !(DataSpaceInst (ModuleData mod))
    }

{- *** The control stack ***

   'Control' is the runtime realisation of the type-level @labels@ environment: the stack of
   what to do when the running code finishes or a branch unwinds to it. Each entry is a block
   or @if@ label ('BlockLabel'), a @loop@ label ('LoopLabel'), a call boundary — the spec's
   /activation frame/ — ('CallBoundary'), or the boundary of the entry function
   ('EntryBoundary'); each label a branch can target corresponds to one entry. It is indexed by

     * @res@    — the result of the whole computation (the entry function),
     * @ret@    — the result of the /current/ activation,
     * @locals@ and @labels@ — the locals and label environment of the running code,
     * @cur@    — the value stack the running code leaves when it falls through to this entry.

   An @Elem rs labels@ branch target therefore selects an entry directly, and unwinding it
   stays type-correct without any coercion.

   The pc stack is a static index: it is threaded through every 'Expr' but no entry of this
   control stack holds it, and no rule of 'step' reads it.

   SecWasm checks most flows during validation, but not memory reads: those are checked at
   run time ('Runtime.MemInst.loadChecked'), a store marks the bytes it writes with its level, and
   @memory.grow@ leaves new pages public. The byte levels live in 'Runtime.MemInst.MemInst'.
-}
data
    Control
        (mod :: ModuleShape)
        (res :: LabelledResultType)
        (ret :: LabelledResultType)
        (locals :: [LabelledValType])
        (labels :: [LabelledResultType])
        (cur :: [LabelledValType])
    where
    {- | The bottom of the stack: the entry activation. Falling through (or @br@ to its only
    label, or @return@) leaving @res@ completes the whole computation.
    -}
    EntryBoundary :: Control mod res res locals '[res] res
    {- | A @block@/@if@ label. On normal completion or a branch to it, put the produced @rs@
    on top of the saved @below@ and run the continuation in the enclosing environment.
    -}
    BlockLabel ::
        !(ValueStack below) ->
        Expr mod ('FrameShape locals ret) labels pcA1 pcB1 (rs ++ below) contOut ->
        Control mod res ret locals labels contOut ->
        Control mod res ret locals (rs ': labels) rs
    {- | A @loop@ label. A branch to it (carrying the loop's parameters) restarts the body;
    normal completion runs the continuation, exactly like 'BlockLabel'.
    -}
    LoopLabel ::
        !(ValueStack below) ->
        Expr mod ('FrameShape locals ret) (ps ': labels) pcA2 pcB2 ps rs ->
        Expr mod ('FrameShape locals ret) labels pcA3 pcB3 (rs ++ below) contOut ->
        Control mod res ret locals labels contOut ->
        Control mod res ret locals (ps ': labels) rs
    {- | A call boundary: the callee's bottom frame. When the callee finishes (or returns),
    put its @rs@ results on the caller's saved stack and resume the caller. The 'Word' is the
    callee's activation depth (see 'activationDepth'), cached here so a call reads the current
    depth off the nearest boundary instead of walking the whole stack.
    -}
    CallBoundary ::
        !Word ->
        !(ValueStack below) ->
        !(LocalSpaceInst callerLocals) ->
        Expr mod ('FrameShape callerLocals callerRet) callerLabels pcA4 pcB4 (rs ++ below) contOut ->
        Control mod res callerRet callerLocals callerLabels contOut ->
        Control mod res rs calleeLocals '[rs] rs

{- | A machine configuration. The instruction sequence runs from @cur@ to @out@; the control
  stack expects exactly the @out@ it leaves. All shape indices are existential; only the
  module signature @mod@ and the overall result @res@ are visible.
-}
data Config (mod :: ModuleShape) (res :: LabelledResultType) where
    Config ::
        !(Store mod) ->
        !(LocalSpaceInst locals) ->
        !(ValueStack cur) ->
        Expr mod ('FrameShape locals ret) labels pcA5 pcB5 cur out ->
        Control mod res ret locals labels out ->
        Config mod res

{- | A call into the host, suspended: which function, its arguments (a stack of exactly its
  parameter shape), the store to perform it against, and how to continue once the results
  are known. The memory constraint travels with it so the driver can read and write memory.

  A host call is where data enters and leaves the module, so it is where a leak finally
  happens. The scalar arguments and results are typed by the policy's declaration of the
  import; the buffers a call reads or writes are checked by the driver against the file
  descriptor's level ("Runtime.Wasi"), the same kind of check as a load's.
-}
data HostRequest (mod :: ModuleShape) (res :: LabelledResultType) where
    HostRequest ::
        (ModuleMems mod ~ (mem ': mems)) =>
        WasiFunc ('LabelledFuncType 'Low hostParams hostResults) ->
        ValueStack hostParams ->
        Store mod ->
        SameValueTypes hostResults rs ->
        Suspended mod res rs ->
        HostRequest mod res
    -- | A call to a 'ForeignFunc': its names, its arguments (public, by their type), and where its results go.
    ForeignRequest ::
        Text ->
        Text ->
        Sing ps ->
        AllPublic ps ->
        ValueStack ps ->
        Sing rs ->
        Store mod ->
        Suspended mod res rs ->
        HostRequest mod res

{- | A configuration with an @rs@-shaped hole where a call's results go: the caller's locals,
  the stack it saved below the arguments, the code after the call and its control stack. The
  'Append' witness says where the results sit on that stack.
-}
data Suspended (mod :: ModuleShape) (res :: LabelledResultType) (rs :: LabelledResultType) where
    Suspended ::
        Append rs below full ->
        LocalSpaceInst locals ->
        ValueStack below ->
        Expr mod ('FrameShape locals ret) labels pcA6 pcB6 full contOut ->
        Control mod res ret locals labels contOut ->
        Suspended mod res rs

-- | Fill the hole: continue the suspended computation with the host's results and store.
resumeWith :: Store mod -> ValueStack rs -> Suspended mod res rs -> Config mod res
resumeWith store results (Suspended witness locals below cont control) =
    Config store locals (appendWith witness results below) cont control

-- *** The step relation ***

{- | The result of running one instruction, indexed by the check its rule depends on
  ('DynamicCheck'): to continue, or to call the host, the machine has to present the evidence
  that the check passed ('CheckPassed'). This is what makes a forgotten check a type error.
  The clause of 'stepInstr' for a load has to produce a @StepResult ('BytesBelow level)@,
  which holds a 'Runtime.MemInst.CheckedRead' at that level, and nothing but the checked read
  makes one; a clause that continued without reading, or after comparing with another level,
  would not have the type. The evidence is strict, so it cannot be left undefined either.
-}
data StepResult (check :: DynamicCheck) (mod :: ModuleShape) (res :: LabelledResultType) where
    Stepped :: !(CheckPassed check) -> !(Config mod res) -> StepResult check mod res
    Done :: !(Store mod) -> !(ValueStack res) -> StepResult 'NoDynamicCheck mod res
    HostCall :: !(CheckPassed check) -> HostRequest mod res -> StepResult check mod res

-- | The result of a step whatever the instruction was: what 'step' returns.
data SomeStepResult (mod :: ModuleShape) (res :: LabelledResultType) where
    SomeStepResult :: StepResult check mod res -> SomeStepResult mod res

-- Inlined, like 'stepInstr', into whoever takes its result apart at once. As a call, every
-- step allocated the @Right (Stepped … (Config …))@ it returns only for the caller to discard
-- it: bench/'s erased machine, where GHC inlines its 'step' because it has one caller, showed
-- that to be the whole of this machine's extra allocation (TODO.md §I, E1). A pragma changes
-- the code GHC emits, not the meaning: 'step' is the same total function.
{-# INLINE step #-}

{- | Advance one configuration. Total over every well-typed configuration: see the module
  header for how this constitutes the progress half of type soundness. The evidence of the
  instruction's check is still inside the result; a driver drops it.

  The drivers below ('run', 'runFor') do not call this. They take the configuration apart
  themselves and call 'stepInstr' and 'popControl' in the branch that has the instruction in
  hand, where GHC sees the result's index and specialises the loop; behind the existential of
  'SomeStepResult' it did not, and every step built its result after all.
-}
step :: FuncSpaceInst mod (ModuleFuncs mod) -> Config mod res -> Either Trap (SomeStepResult mod res)
step funcs (Config store locals stack code control) = case code of
    INil -> Right (SomeStepResult (popControl store locals stack control))
    instr :. rest -> case stepInstr funcs store locals stack instr rest control of
        Left trap -> Left trap
        Right result -> Right (SomeStepResult result)

{-# INLINE stepInstr #-}

{- | Run one instruction against the state it finds: the store, the locals, the stack, the
  code after it and the control stack. The result is indexed by the instruction's check, so
  each clause has to present the evidence its instruction asks for.
-}
stepInstr ::
    FuncSpaceInst mod (ModuleFuncs mod) ->
    Store mod ->
    LocalSpaceInst locals ->
    ValueStack stackIn ->
    Instr mod ('FrameShape locals ret) labels pcIn pcOut check stackIn stackOut ->
    Expr mod ('FrameShape locals ret) labels pcOut pcEnd stackOut out ->
    Control mod res ret locals labels out ->
    Either Trap (StepResult check mod res)
stepInstr funcs store locals stack instr rest control = case instr of
    {- Constants & numeric -}
    IConst _ literal -> stepped NothingToCheck store locals (literal :# stack) rest control
    IAdd nt -> stepBin NothingToCheck store locals stack (numBinary nt (+)) rest control
    ISub nt -> stepBin NothingToCheck store locals stack (numBinary nt (-)) rest control
    IMul nt -> stepBin NothingToCheck store locals stack (numBinary nt (*)) rest control
    IDiv sn -> case stack of
        b :# a :# r -> case numDiv sn a b of
            Right v -> stepped NothingToCheck store locals (v :# r) rest control
            Left t -> Left t
    IRem nt sign -> case stack of
        b :# a :# r -> case numRem nt sign a b of
            Right v -> stepped NothingToCheck store locals (v :# r) rest control
            Left t -> Left t
    {- Comparison -}
    IEqz nt -> stepUn NothingToCheck store locals stack (numEqz nt) rest control
    IEq nt -> stepBin NothingToCheck store locals stack (numEqNe (==) nt) rest control
    INe nt -> stepBin NothingToCheck store locals stack (numEqNe (/=) nt) rest control
    ILt sn -> stepBin NothingToCheck store locals stack (numCompare (<) sn) rest control
    IGt sn -> stepBin NothingToCheck store locals stack (numCompare (>) sn) rest control
    ILe sn -> stepBin NothingToCheck store locals stack (numCompare (<=) sn) rest control
    IGe sn -> stepBin NothingToCheck store locals stack (numCompare (>=) sn) rest control
    {- Conversions -}
    IConvert op -> case stack of
        v :# r -> case convertVal op v of
            Right result -> stepped NothingToCheck store locals (result :# r) rest control
            Left t -> Left t
    {- Integer bitwise / shift / count, floating-point unary / binary -}
    IBitwise nt op -> stepBin NothingToCheck store locals stack (bitwiseT nt op) rest control
    ICount nt op -> stepUn NothingToCheck store locals stack (countT nt op) rest control
    IFloatUn nt op -> stepUn NothingToCheck store locals stack (floatUnT nt op) rest control
    IFloatBin nt op -> stepBin NothingToCheck store locals stack (floatBinT nt op) rest control
    {- Memory size / grow & narrow access -}
    IMemSize -> stepped NothingToCheck store locals (memoryPages (currentMem store) :# stack) rest control
    IMemGrow _ -> case stack of
        delta :# r ->
            let mem = currentMem store
             in case growMemory delta mem of
                    Just grown -> stepped NothingToCheck (storeMem grown store) locals (memoryPages mem :# r) rest control
                    Nothing -> stepped NothingToCheck store locals (growFailed :# r) rest control
    ILoadN level site nw sign memArg -> case stack of
        addr :# r ->
            case loadChecked (currentMem store) level (effectiveAddr addr memArg) (narrowBytes nw) of
                Right checked -> stepped (BytesWereBelow checked) store locals (narrowLoadT nw sign (checkedWord checked) :# r) rest control
                Left failure -> Left (loadTrap site failure)
    IStoreN level _ nw memArg -> case stack of
        value :# addr :# r ->
            case storeWordAt (fromSing level) (currentMem store) (effectiveAddr addr memArg) (narrowBytes nw) (narrowStoreT nw value) of
                Just mem' -> stepped NothingToCheck (storeMem mem' store) locals r rest control
                Nothing -> Left OutOfBoundsMemoryAccess
    {- Bulk memory: each checks both ranges before writing anything -}
    IMemCopy level -> case stack of
        count :# src :# dst :# r ->
            case copyWithinAt (fromSing level) (fromIntegral dst) (fromIntegral src) (fromIntegral count) (currentMem store) of
                Just mem' -> stepped NothingToCheck (storeMem mem' store) locals r rest control
                Nothing -> Left OutOfBoundsMemoryAccess
    IMemFill level -> case stack of
        count :# value :# dst :# r ->
            case fillBytesAt (fromSing level) (fromIntegral dst) (fromIntegral value) (fromIntegral count) (currentMem store) of
                Just mem' -> stepped NothingToCheck (storeMem mem' store) locals r rest control
                Nothing -> Left OutOfBoundsMemoryAccess
    IMemInit level segmentIx -> case stack of
        count :# srcOffset :# dst :# r ->
            let segment = fromMaybe BS.empty (getSegment segmentIx store.dataSegments)
                n = fromIntegral count
                src = fromIntegral srcOffset
                inSegment = src + n <= BS.length segment
                written = writeBytesAt (fromSing level) (currentMem store) (fromIntegral dst) (BS.unpack (BS.take n (BS.drop src segment)))
             in case (inSegment, written) of
                    (True, Just mem') -> stepped NothingToCheck (storeMem mem' store) locals r rest control
                    _ -> Left OutOfBoundsMemoryAccess
    IDataDrop segmentIx -> stepped NothingToCheck (storeDropSegment segmentIx store) locals stack rest control
    {- References and tables. A reference is a word like any other value; the table
       instructions trap on an index past the table (or past the segment), and otherwise move
       references between a table, the stack and an element segment unchanged. -}
    IRefNull isRef -> withReference isRef (stepped NothingToCheck store locals (nullReference :# stack) rest control)
    IRefFunc function -> stepped NothingToCheck store locals (functionReference function :# stack) rest control
    IRefIsNull isRef -> case stack of
        reference :# r -> stepped NothingToCheck store locals ((if withReference isRef (isNullReference reference) then 1 else 0) :# r) rest control
    ITableGet isRef tableIx -> withReference isRef $ case stack of
        index :# r -> case getEntry (getTable tableIx store.tables) index of
            Just reference -> stepped NothingToCheck store locals (reference :# r) rest control
            Nothing -> Left OutOfBoundsTableAccess
    ITableSet isRef _ tableIx -> withReference isRef $ case stack of
        reference :# index :# r -> case setEntry index reference (getTable tableIx store.tables) of
            Just table -> stepped NothingToCheck (storeTable tableIx table store) locals r rest control
            Nothing -> Left OutOfBoundsTableAccess
    ITableSize tableIx -> stepped NothingToCheck store locals (tableSize (getTable tableIx store.tables) :# stack) rest control
    -- (As for @memory.grow@, failing to grow is not a trap: the result is -1.)
    ITableGrow isRef _ tableIx -> withReference isRef $ case stack of
        count :# reference :# r ->
            let table = getTable tableIx store.tables
             in case growTable count reference table of
                    Just grown -> stepped NothingToCheck (storeTable tableIx grown store) locals (tableSize table :# r) rest control
                    Nothing -> stepped NothingToCheck store locals (0xFFFFFFFF :# r) rest control
    ITableFill isRef _ tableIx -> withReference isRef $ case stack of
        count :# reference :# index :# r -> case fillEntries index count reference (getTable tableIx store.tables) of
            Just table -> stepped NothingToCheck (storeTable tableIx table store) locals r rest control
            Nothing -> Left OutOfBoundsTableAccess
    -- (The source is read whole before the destination is written, so the two may overlap.)
    ITableCopy _ toIx fromIx -> case stack of
        count :# src :# dst :# r -> case readEntries src count (getTable fromIx store.tables) >>= \references -> writeEntries dst references (getTable toIx store.tables) of
            Just table -> stepped NothingToCheck (storeTable toIx table store) locals r rest control
            Nothing -> Left OutOfBoundsTableAccess
    ITableInit _ segmentIx tableIx -> case stack of
        count :# src :# dst :# r ->
            let segment = getElements segmentIx store.tables
                inSegment = toInteger src + toInteger count <= toInteger (length segment)
                references = take (fromIntegral count) (drop (fromIntegral src) segment)
             in case (inSegment, writeEntries dst references (getTable tableIx store.tables)) of
                    (True, Just table) -> stepped NothingToCheck (storeTable tableIx table store) locals r rest control
                    _ -> Left OutOfBoundsTableAccess
    IElemDrop segmentIx -> stepped NothingToCheck (storeDropElements segmentIx store) locals stack rest control
    {- Stack management -}
    IDrop -> case stack of _ :# r -> stepped NothingToCheck store locals r rest control
    ISelect -> case stack of
        cond :# second :# first :# r ->
            stepped NothingToCheck store locals ((if cond /= 0 then first else second) :# r) rest control
    {- Locals & globals -}
    ILocalGet ix -> stepped NothingToCheck store locals (getLocal ix locals :# stack) rest control
    ILocalSet _ _ ix -> case stack of v :# r -> stepped NothingToCheck store (setLocal ix v locals) r rest control
    ILocalTee _ _ ix -> case stack of v :# _ -> stepped NothingToCheck store (setLocal ix v locals) stack rest control
    IGlobalGet ix -> stepped NothingToCheck store locals (getGlobal ix (store.globals) :# stack) rest control
    IGlobalSet _ _ ix -> case stack of
        v :# r -> stepped NothingToCheck (storeSetGlobal ix v store) locals r rest control
    IGlobalSetPreserved _ ix -> case stack of
        v :# r -> stepped NothingToCheck (storeSetGlobal ix v store) locals r rest control
    {- The preserved globals must hold what was recorded where the construct began -}
    IRequireRestored recorded
        | stillRestored recorded store.globals -> stepped NothingToCheck store locals stack rest control
        | otherwise -> Left GlobalNotRestored
    {- Memory -}
    ILoad level site nt memArg -> case stack of
        addr :# r ->
            case loadChecked (currentMem store) level (effectiveAddr addr memArg) (numBytes nt) of
                Right checked -> stepped (BytesWereBelow checked) store locals (loadValue nt (checkedWord checked) :# r) rest control
                Left failure -> Left (loadTrap site failure)
    IStore level _ nt memArg -> case stack of
        value :# addr :# r ->
            case storeWordAt (fromSing level) (currentMem store) (effectiveAddr addr memArg) (numBytes nt) (storedWord nt value) of
                Just mem' -> stepped NothingToCheck (storeMem mem' store) locals r rest control
                Nothing -> Left OutOfBoundsMemoryAccess
    {- Relabelling changes the level in the type only: the same word goes back on the stack -}
    IRelabel _ -> case stack of
        v :# r -> stepped NothingToCheck store locals (v :# r) rest control
    IDeclassify -> case stack of
        v :# r -> stepped NothingToCheck store locals (v :# r) rest control
    IRelabelResults flows -> stepped NothingToCheck store locals (relabelStack flows stack) rest control
    {- Calls: enter the callee (see 'enterCall'). An indirect call reads the table entry through
       'lookupChecked', which compares its type with the expected one: the labelled parameters
       and results must be the same, and the expected bound must flow into the callee's
       (SecWasm's ℓf ⊑ ℓt), since the call's pc was checked against the expected bound only.
       The callee it enters is the one that lookup hands out, and so is its evidence. -}
    ICall _ flows _ witness ix -> enterCall NothingToCheck funcs store locals flows witness ix stack rest control
    ICallIndirect tableIx _ flows _ witness expected -> case stack of
        index :# below' -> case lookupChecked store.tables.directory (getTable tableIx store.tables) index expected of
            Left trap -> Left trap
            Right checked -> enteredCallee checked $ \ix ->
                enterCall (CalleeWasWithin checked) funcs store locals flows witness ix below' rest control
    {- Structured control: push the matching frame and run the body -}
    -- (What follows the construct is forced before the label holds it: left lazy, every block
    -- entered would allocate the suspended choice of 'restoring'.)
    IBlock _ _ restores flows witness body ->
        let (params, below) = splitStack witness stack
            !after = restoring restores store rest
         in Right (Stepped NothingToCheck (Config store locals (relabelStack flows params) body (BlockLabel below after control)))
    ILoop _ restores _ _ flows witness body ->
        let (params, below) = splitStack witness stack
            !after = restoring restores store rest
         in Right (Stepped NothingToCheck (Config store locals (relabelStack flows params) body (LoopLabel below body after control)))
    IIf _ _ restores flows witness thenArm elseArm -> case stack of
        cond :# below' ->
            let (params, below) = splitStack witness below'
                !after = restoring restores store rest
             in Right . Stepped NothingToCheck $
                    if cond /= 0
                        then Config store locals (relabelStack flows params) thenArm (BlockLabel below after control)
                        else Config store locals (relabelStack flows params) elseArm (BlockLabel below after control)
    {- Branches: unwind the control stack to the targeted frame -}
    IBr _ flows witness target -> let (vs, _) = splitStack witness stack in Right (unwind store locals target (relabelStack flows vs) control)
    IBrIf _ flows witness fallThrough target -> case stack of
        cond :# below'
            | cond /= 0 ->
                let (vs, _) = splitStack witness below'
                 in Right (unwind store locals target (relabelStack flows vs) control)
            | otherwise -> case fallThrough of
                KeepsLevels -> stepped NothingToCheck store locals below' rest control
                TakesTargetType ->
                    let (vs, below) = splitStack witness below'
                     in stepped NothingToCheck store locals (appendStack (relabelStack flows vs) below) rest control
    IBrTable _ flows witness reach targets def -> case stack of
        idx :# below' ->
            let target = withinReach reach (case drop (fromIntegral idx) targets of t : _ -> t; [] -> def)
                (vs, _) = splitStack witness below'
             in Right (unwindTo store locals target (relabelStack flows vs) control)
    IReturn _ flows witness ->
        let (vs, _) = splitStack witness stack in Right (returnUnwind store locals (relabelStack flows vs) control)
    {- Inert -}
    INop -> stepped NothingToCheck store locals stack rest control
    IUnreachable -> Left UnreachableExecuted

{- | Enter a function: for a WebAssembly function, push a call boundary and start its body over
  an empty stack; for a host function, hand the call out as a request with the caller suspended
  around it. The 'Append' witness peels the arguments off the stack. The evidence is the
  calling instruction's: nothing for a direct call, the checked callee for an indirect one.
-}

-- Inlined into its two call sites, so that the driver sees the 'Stepped' a call ends in and
-- does not build it: 16 % less allocation on a call-heavy kernel (bench/tripwire.py, fib).
{-# INLINE enterCall #-}
enterCall ::
    CheckPassed check ->
    FuncSpaceInst mod (ModuleFuncs mod) ->
    Store mod ->
    LocalSpaceInst locals ->
    SegmentFlows args ps ->
    Append args s full ->
    Elem ('LabelledFuncType bound ps rs) (ModuleFuncs mod) ->
    ValueStack full ->
    Expr mod ('FrameShape locals ret) labels pcA7 pcB7 (rs ++ s) out ->
    Control mod res ret locals labels out ->
    Either Trap (StepResult check mod res)
enterCall evidence funcs store locals flows witness ix stack rest control = case getFunc ix funcs of
    WasmFunc (Function params declared returns body)
        | depth > callDepthBound -> Left CallStackExhausted
        | otherwise ->
            let (args, below) = splitStack witness stack
                calleeLocals = seedLocals flows params declared args
                !after = restoringOnReturn returns store rest
             in Right (Stepped evidence (Config store calleeLocals VNil body (CallBoundary depth below locals after control)))
    HostFunc wasiFunc argsAgree resultsAgree ->
        let (args, below) = splitStack witness stack
            suspended = Suspended (appendFromSameValues resultsAgree) locals below rest control
         in Right (HostCall evidence (HostRequest wasiFunc (relabelStack argsAgree (relabelStack flows args)) store resultsAgree suspended))
    ForeignFunc moduleName fieldName params results allPublic ->
        let (args, below) = splitStack witness stack
            suspended = Suspended (appendFromSing results) locals below rest control
         in Right (HostCall evidence (ForeignRequest moduleName fieldName params allPublic (relabelStack flows args) results store suspended))
    GhostFunc -> Left InformationFlowViolation
  where
    depth = activationDepth control + 1

-- | The 'Append' witness for a result segment whose shape a 'SameValueTypes' witness gives.
appendFromSameValues :: SameValueTypes hostResults rs -> Append rs below (rs ++ below)
appendFromSameValues NoValues = ANil
appendFromSameValues (SameValue rest) = ACons (appendFromSameValues rest)

appendNilSameValues :: SameValueTypes hostResults rs -> Append rs '[] rs
appendNilSameValues NoValues = ANil
appendNilSameValues (SameValue rest) = ACons (appendNilSameValues rest)

{- | What follows a block, loop or conditional, behind the comparison of the preserved globals
  if the construct has to restore them ('Restores'): their values now, at its start, are
  recorded in an 'IRequireRestored' that runs first when control comes out of it, by falling
  out of its end or by a branch to its label. A branch further out skips the comparison, and
  the construct it lands behind has its own. A module without preserved globals records nothing.
-}
{-# INLINE restoring #-}
restoring ::
    Restores pcEnd pcsAfter (ModuleGlobals mod) ->
    Store mod ->
    Expr mod frame labels pcA pcB cur out ->
    Expr mod frame labels pcA pcB cur out
restoring restores store rest = case restores of
    PcDoesNotDrop _ -> rest
    PreservedRestored which -> comparingAfter which store rest

-- | The same for what follows a call, if the callee may return under a secret pc ('ReturnsWith').
{-# INLINE restoringOnReturn #-}
restoringOnReturn ::
    ReturnsWith pcOut (ModuleGlobals mod) ->
    Store mod ->
    Expr mod frame labels pcA pcB cur out ->
    Expr mod frame labels pcA pcB cur out
restoringOnReturn returns store rest = case returns of
    ReturnsUnderPublicPc -> rest
    RestoresOnReturn which -> comparingAfter which store rest

comparingAfter ::
    PreservedOf (ModuleGlobals mod) ->
    Store mod ->
    Expr mod frame labels pcA pcB cur out ->
    Expr mod frame labels pcA pcB cur out
comparingAfter which store rest = case recordPreserved which store.globals of
    Nothing -> rest
    Just recorded -> IRequireRestored recorded :. rest

{- | The most activations the machine allows on the control stack at once; a call that would
  open one more traps with 'CallStackExhausted'. The spec leaves the bound to the implementation
  and only requires exhaustion to be a trap rather than a crash; without one, a runaway recursion
  grows the heap-allocated control stack until memory runs out.
-}
callDepthBound :: Word
callDepthBound = 10000

{- | The depth of the running activation: the entry activation is 1, and each 'CallBoundary'
  caches the depth of the activation it opened, so the walk only crosses the current
  activation's labels.
-}
activationDepth :: Control mod res ret locals labels cur -> Word
activationDepth control = case control of
    EntryBoundary -> 1
    CallBoundary depth _ _ _ _ -> depth
    BlockLabel _ _ rest -> activationDepth rest
    LoopLabel _ _ _ rest -> activationDepth rest

{- | The "continue in the current frame" case: a successor configuration, with the evidence of
  the instruction's check. The evidence is an argument, here and in 'stepBin' and 'stepUn', and
  not fixed to 'NothingToCheck' with the loads wrapping their own, for GHC's sake. A clause of
  'stepInstr' has to produce a @StepResult check@; when a helper produces a
  @StepResult 'NoDynamicCheck@ instead, the clause's result is that value under a coercion,
  SpecConstr does not see the constructor through it, and the driver builds the 'Stepped' and
  the 'Config' of every step after all: 9 to 74 % more allocation on bench/tripwire.py's
  workloads (2026-10-05). With the coercion on the evidence, a static closure, the result is
  a bare constructor application.
-}
stepped ::
    CheckPassed check ->
    Store mod ->
    LocalSpaceInst locals ->
    ValueStack si ->
    Expr mod ('FrameShape locals ret) labels pcA8 pcB8 si out ->
    Control mod res ret locals labels out ->
    Either Trap (StepResult check mod res)
stepped evidence store locals stack code control = Right (Stepped evidence (Config store locals stack code control))

-- | Pop two same-typed operands (@a@ below, @b@ on top), push @op a b@, and continue.
stepBin ::
    CheckPassed check ->
    Store mod ->
    LocalSpaceInst locals ->
    ValueStack ((x ':~ lb) ': (x ':~ la) ': s) ->
    (HostType x -> HostType x -> HostType z) ->
    Expr mod ('FrameShape locals ret) labels pcX pcY ((z ':~ l) ': s) out ->
    Control mod res ret locals labels out ->
    Either Trap (StepResult check mod res)
stepBin evidence store locals (b :# a :# r) op = stepped evidence store locals (op a b :# r)

-- | Pop one operand, push @op a@, and continue.
stepUn ::
    CheckPassed check ->
    Store mod ->
    LocalSpaceInst locals ->
    ValueStack ((x ':~ la) ': s) ->
    (HostType x -> HostType z) ->
    Expr mod ('FrameShape locals ret) labels pcX pcY ((z ':~ l) ': s) out ->
    Control mod res ret locals labels out ->
    Either Trap (StepResult check mod res)
stepUn evidence store locals (a :# r) op = stepped evidence store locals (op a :# r)

-- | The trap of a load that yielded no word; a secret read names the load's site.
loadTrap :: AccessSite -> LoadFailure -> Trap
loadTrap site failure = case failure of
    LoadOutOfBounds -> OutOfBoundsMemoryAccess
    LoadAboveLevel -> SecretRead site

{- | The module's single memory, and a store update for it. The @ModuleMems mod ~ (m ': ms)@
  constraint every memory instruction carries makes both total.
-}
currentMem :: (ModuleMems mod ~ (m ': ms)) => Store mod -> MemInst m
currentMem store = firstMem store.memories

storeMem :: (ModuleMems mod ~ (m ': ms)) => MemInst m -> Store mod -> Store mod
storeMem mem store =
    Store {globals = store.globals, memories = setFirstMem mem store.memories, tables = store.tables, dataSegments = store.dataSegments}

-- The store's other updates. (Its field names are shared with 'ModuleInst', so the records are
-- rebuilt rather than updated: GHC no longer disambiguates such updates by type.)
storeSetGlobal :: Elem ('GlobalType mut (t ':~ l)) (ModuleGlobals mod) -> HostType t -> Store mod -> Store mod
storeSetGlobal ix v store =
    Store {globals = setGlobal ix v store.globals, memories = store.memories, tables = store.tables, dataSegments = store.dataSegments}

storeTable :: Elem t (ModuleTables mod) -> TableInst -> Store mod -> Store mod
storeTable ix table store =
    Store {globals = store.globals, memories = store.memories, tables = setTable ix table store.tables, dataSegments = store.dataSegments}

storeDropElements :: Elem ('ElemShape t) (ModuleElems mod) -> Store mod -> Store mod
storeDropElements ix store =
    Store {globals = store.globals, memories = store.memories, tables = dropElements ix store.tables, dataSegments = store.dataSegments}

storeDropSegment :: Elem 'DataShape (ModuleData mod) -> Store mod -> Store mod
storeDropSegment ix store =
    Store {globals = store.globals, memories = store.memories, tables = store.tables, dataSegments = dropSegment ix store.dataSegments}

-- | What @memory.grow@ pushes when it cannot grow: the spec's @-1@, as an unsigned i32.
growFailed :: Word32
growFailed = 0xFFFFFFFF

{- | The effective byte address of a memory access: dynamic base + static @offset@, computed
  in 'Int' so it cannot wrap around 2^32. An over-large address then traps in
  'readBytes'/'writeBytes' instead of silently aliasing a wrapped-around address.
-}
effectiveAddr :: Word32 -> MemArg -> Int
effectiveAddr base memArg = fromIntegral base + fromIntegral memArg.offset

{- | Resume the enclosing computation: put the produced values @vs@ on top of the frame's
  saved @below@ stack and run its continuation. Shared by every frame that completes.
-}
resume ::
    Store mod ->
    LocalSpaceInst locals ->
    ValueStack rs ->
    ValueStack below ->
    Expr mod ('FrameShape locals ret) labels pcA9 pcB9 (rs ++ below) contOut ->
    Control mod res ret locals labels contOut ->
    StepResult 'NoDynamicCheck mod res
resume store locals vs below cont rest = Stepped NothingToCheck (Config store locals (appendStack vs below) cont rest)

-- | The current sequence reached its end (left @cur@): hand control to the top frame.
popControl ::
    Store mod ->
    LocalSpaceInst locals ->
    ValueStack cur ->
    Control mod res ret locals labels cur ->
    StepResult 'NoDynamicCheck mod res
popControl store _ vs EntryBoundary = Done store vs
popControl store locals vs (BlockLabel below cont rest) = resume store locals vs below cont rest
popControl store locals vs (LoopLabel below _ cont rest) = resume store locals vs below cont rest
popControl store _ vs (CallBoundary _ below cl cont cf) = resume store cl vs below cont cf

{- | Unwind to the @ix@-th enclosing label, carrying that label's values. A block/if label
  resumes after the construct; a loop label restarts the body; the function's own label
  returns from it.
-}
unwind ::
    Store mod ->
    LocalSpaceInst locals ->
    BranchTarget l rs labels pcs pcs' ->
    ValueStack rs ->
    Control mod res ret locals labels cur ->
    StepResult 'NoDynamicCheck mod res
unwind store _ TargetHere vs EntryBoundary = Done store vs
unwind store locals TargetHere vs (BlockLabel below cont rest) = resume store locals vs below cont rest
unwind store locals TargetHere vs (LoopLabel below body cont rest) =
    Stepped NothingToCheck (Config store locals vs body (LoopLabel below body cont rest))
unwind store _ TargetHere vs (CallBoundary _ below cl cont cf) = resume store cl vs below cont cf
unwind store locals (TargetThere ix') vs (BlockLabel _ _ rest) = unwind store locals ix' vs rest
unwind store locals (TargetThere ix') vs (LoopLabel _ _ _ rest) = unwind store locals ix' vs rest
unwind _ _ (TargetThere ix') _ (CallBoundary {}) = case ix' of {}
unwind _ _ (TargetThere ix') _ EntryBoundary = case ix' of {}

-- | 'unwind' for @br_table@, whose targets are plain label indices.
unwindTo ::
    Store mod ->
    LocalSpaceInst locals ->
    Elem rs labels ->
    ValueStack rs ->
    Control mod res ret locals labels cur ->
    StepResult 'NoDynamicCheck mod res
unwindTo store _ Here vs EntryBoundary = Done store vs
unwindTo store locals Here vs (BlockLabel below cont rest) = resume store locals vs below cont rest
unwindTo store locals Here vs (LoopLabel below body cont rest) =
    Stepped NothingToCheck (Config store locals vs body (LoopLabel below body cont rest))
unwindTo store _ Here vs (CallBoundary _ below cl cont cf) = resume store cl vs below cont cf
unwindTo store locals (There ix') vs (BlockLabel _ _ rest) = unwindTo store locals ix' vs rest
unwindTo store locals (There ix') vs (LoopLabel _ _ _ rest) = unwindTo store locals ix' vs rest
unwindTo _ _ (There ix') _ (CallBoundary {}) = case ix' of {}
unwindTo _ _ (There ix') _ EntryBoundary = case ix' of {}

-- | @return@: unwind past every label frame in the current activation to the call boundary.
returnUnwind ::
    Store mod ->
    LocalSpaceInst locals ->
    ValueStack ret ->
    Control mod res ret locals labels cur ->
    StepResult 'NoDynamicCheck mod res
returnUnwind store _ vs EntryBoundary = Done store vs
returnUnwind store _ vs (CallBoundary _ below cl cont cf) = resume store cl vs below cont cf
returnUnwind store locals vs (BlockLabel _ _ rest) = returnUnwind store locals vs rest
returnUnwind store locals vs (LoopLabel _ _ _ rest) = returnUnwind store locals vs rest

-- | The mutable state of an instantiated module, and the module with that state put back.
moduleToStore :: ModuleInst mod -> Store mod
moduleToStore tm = Store {globals = tm.globals, memories = tm.memories, tables = tm.tables, dataSegments = tm.dataSegments}

storeToModule :: FuncSpaceInst mod (ModuleFuncs mod) -> Store mod -> ModuleInst mod
storeToModule funcs store =
    ModuleInst {functions = funcs, globals = store.globals, memories = store.memories, tables = store.tables, dataSegments = store.dataSegments}

-- | Where a run stops: with its results and final store, or waiting for the host.
data Halt (mod :: ModuleShape) (res :: LabelledResultType) where
    Finished :: Store mod -> ValueStack res -> Halt mod res
    AwaitingHost :: HostRequest mod res -> Halt mod res

{- | Iterate 'step' until the computation finishes or needs the host. (This is the only partial
  function here — it loops, which is termination, a property orthogonal to the progress and
  preservation that 'step' carries.)
-}
run :: FuncSpaceInst mod (ModuleFuncs mod) -> Config mod res -> Either Trap (Halt mod res)
run funcs (Config store locals stack code control) = case code of
    INil -> case popControl store locals stack control of
        Done store' vs -> Right (Finished store' vs)
        HostCall _ request -> Right (AwaitingHost request)
        Stepped _ next -> run funcs next
    instr :. rest -> case stepInstr funcs store locals stack instr rest control of
        Left t -> Left t
        Right (Done store' vs) -> Right (Finished store' vs)
        Right (HostCall _ request) -> Right (AwaitingHost request)
        Right (Stepped _ next) -> run funcs next

-- | How a fuel-bounded run ends: halted like 'run', or stopped with the budget spent.
data Fuelled (mod :: ModuleShape) (res :: LabelledResultType) where
    Halted :: Halt mod res -> Fuelled mod res
    OutOfFuel :: Config mod res -> Fuelled mod res

{- | 'run' with a budget of steps, so a test can state that a program terminates (or does
  not) within it; unlike 'run' this is total.
-}
runFor :: Int -> FuncSpaceInst mod (ModuleFuncs mod) -> Config mod res -> Either Trap (Fuelled mod res)
runFor fuel funcs config@(Config store locals stack code control)
    | fuel <= 0 = Right (OutOfFuel config)
    | otherwise = case code of
        INil -> case popControl store locals stack control of
            Done store' vs -> Right (Halted (Finished store' vs))
            HostCall _ request -> Right (Halted (AwaitingHost request))
            Stepped _ next -> runFor (fuel - 1) funcs next
        instr :. rest -> case stepInstr funcs store locals stack instr rest control of
            Left t -> Left t
            Right (Done store' vs) -> Right (Halted (Finished store' vs))
            Right (HostCall _ request) -> Right (Halted (AwaitingHost request))
            Right (Stepped _ next) -> runFor (fuel - 1) funcs next

-- | How a function invocation ends: with the module as the call left it, or needing the host.
data Outcome (mod :: ModuleShape) (rs :: LabelledResultType) where
    Completed :: ModuleInst mod -> ValueStack rs -> Outcome mod rs
    NeedsHost :: HostRequest mod rs -> Outcome mod rs

{- | Run a function against an instantiated module: seed the entry activation and iterate.
  The module comes back with its globals and memories as the call left them, so state
  persists from one invocation to the next; on a trap the caller keeps the module it had.
  Calling a host function directly (an exported import) is a request straight away.
-}
runFunction ::
    Sing (rs :: [LabelledValType]) ->
    ModuleInst mod ->
    FuncInst mod ('LabelledFuncType bound ps rs) ->
    ValueStack ps ->
    Either Trap (Outcome mod rs)
runFunction resultTypes tm (WasmFunc (Function params declared returns body)) args = do
    halt <- run (tm.functions) (Config store locals VNil body entry)
    Right $ case halt of
        Finished store' results ->
            Completed (storeToModule tm.functions store') results
        AwaitingHost request -> NeedsHost request
  where
    store = moduleToStore tm
    locals = seedLocals (segmentSelf params) params declared args
    -- The entry function is held to what every callee is: if it may return under a secret
    -- pc, it returns behind a comparison of the preserved globals with their values now.
    -- The comparison sits in a call boundary of its own, over the entry boundary.
    entry = case appendIs (appendNil resultTypes) of
        Refl -> case restoringOnReturn returns store INil of
            INil -> EntryBoundary
            comparison -> CallBoundary 1 VNil noLocals comparison EntryBoundary
runFunction _ tm (HostFunc wasiFunc argsAgree resultsAgree) args =
    let store = moduleToStore tm
     in Right (NeedsHost (HostRequest wasiFunc (relabelStack argsAgree args) store resultsAgree (Suspended (appendNilSameValues resultsAgree) noLocals VNil INil EntryBoundary)))
runFunction _ tm (ForeignFunc moduleName fieldName params results allPublic) args =
    Right (NeedsHost (ForeignRequest moduleName fieldName params allPublic args results (moduleToStore tm) (Suspended (appendNil results) noLocals VNil INil EntryBoundary)))
runFunction _ _ GhostFunc _ = Left InformationFlowViolation

{- *** Numeric dispatch ***

   Each helper dispatches on the singleton (or integer/float witness) the instruction
   carries; matching it refines @HostType t@ to a concrete host type, so the
   operation is total over exactly the cases that can occur.
-}

numBinary ::
    IsNum t ->
    (forall a. Num a => a -> a -> a) ->
    HostType t ->
    HostType t ->
    HostType t
numBinary I32IsNum op a b = op a b
numBinary I64IsNum op a b = op a b
numBinary F32IsNum op a b = op a b
numBinary F64IsNum op a b = op a b

numDiv ::
    NumWithSign t ->
    HostType t ->
    HostType t ->
    Either Trap (HostType t)
numDiv (IntsHaveSign I32IsInt sign) a b = intDiv32 sign a b
numDiv (IntsHaveSign I64IsInt sign) a b = intDiv64 sign a b
numDiv (FloatsHaveNoSign F32IsFloat) a b = Right (a / b)
numDiv (FloatsHaveNoSign F64IsFloat) a b = Right (a / b)

numRem ::
    IsInt t ->
    Signedness ->
    HostType t ->
    HostType t ->
    Either Trap (HostType t)
numRem I32IsInt sign a b = intRem32 sign a b
numRem I64IsInt sign a b = intRem64 sign a b

{- | The ordered comparisons (@lt@/@gt@/@le@/@ge@): signed vs. unsigned on integers, plain on
  floats — driven by the 'NumWithSign' witness, so no signedness ever reaches a float compare.
-}
numCompare ::
    (forall a. Ord a => a -> a -> Bool) ->
    NumWithSign t ->
    HostType t ->
    HostType t ->
    HostType 'I32
numCompare cmp (IntsHaveSign I32IsInt Signed) a b = boolWord (cmp (toSigned32 a) (toSigned32 b))
numCompare cmp (IntsHaveSign I32IsInt Unsigned) a b = boolWord (cmp a b)
numCompare cmp (IntsHaveSign I64IsInt Signed) a b = boolWord (cmp (toSigned64 a) (toSigned64 b))
numCompare cmp (IntsHaveSign I64IsInt Unsigned) a b = boolWord (cmp a b)
numCompare cmp (FloatsHaveNoSign F32IsFloat) a b = boolWord (cmp a b)
numCompare cmp (FloatsHaveNoSign F64IsFloat) a b = boolWord (cmp a b)

-- | Equality/inequality (@eq@/@ne@): no signedness on either integers or floats.
numEqNe ::
    (forall a. Eq a => a -> a -> Bool) ->
    IsNum t ->
    HostType t ->
    HostType t ->
    HostType 'I32
numEqNe cmp I32IsNum a b = boolWord (cmp a b)
numEqNe cmp I64IsNum a b = boolWord (cmp a b)
numEqNe cmp F32IsNum a b = boolWord (cmp a b)
numEqNe cmp F64IsNum a b = boolWord (cmp a b)

numEqz :: IsInt t -> HostType t -> HostType 'I32
numEqz I32IsInt a = boolWord (a == 0)
numEqz I64IsInt a = boolWord (a == 0)

boolWord :: Bool -> Word32
boolWord True = 1
boolWord False = 0

-- *** Memory <-> value marshalling ***

loadValue :: IsNum t -> Word64 -> HostType t
loadValue I32IsNum = fromIntegral
loadValue I64IsNum = id
loadValue F32IsNum = castWord32ToFloat . fromIntegral
loadValue F64IsNum = castWord64ToDouble

storedWord :: IsNum t -> HostType t -> Word64
storedWord I32IsNum = fromIntegral
storedWord I64IsNum = id
storedWord F32IsNum = fromIntegral . castFloatToWord32
storedWord F64IsNum = castDoubleToWord64

-- *** Bitwise / count / float / narrow-memory helpers ***

bitwiseT ::
    IsInt t ->
    BitwiseOp ->
    HostType t ->
    HostType t ->
    HostType t
bitwiseT I32IsInt op a b = bitwise32 op a b
bitwiseT I64IsInt op a b = bitwise64 op a b

bitwise32 :: BitwiseOp -> Word32 -> Word32 -> Word32
bitwise32 op a b = case op of
    BwAnd -> a .&. b
    BwOr -> a .|. b
    BwXor -> a `xor` b
    BwShl -> a `shiftL` modBits 32 b
    BwShr Unsigned -> a `shiftR` modBits 32 b
    BwShr Signed -> fromSigned32 (toSigned32 a `shiftR` modBits 32 b)
    BwRotl -> rotateL a (modBits 32 b)
    BwRotr -> rotateR a (modBits 32 b)

bitwise64 :: BitwiseOp -> Word64 -> Word64 -> Word64
bitwise64 op a b = case op of
    BwAnd -> a .&. b
    BwOr -> a .|. b
    BwXor -> a `xor` b
    BwShl -> a `shiftL` modBits 64 b
    BwShr Unsigned -> a `shiftR` modBits 64 b
    BwShr Signed -> fromSigned64 (toSigned64 a `shiftR` modBits 64 b)
    BwRotl -> rotateL a (modBits 64 b)
    BwRotr -> rotateR a (modBits 64 b)

modBits :: Integral a => Int -> a -> Int
modBits width n = fromIntegral n `mod` width

countT :: IsInt t -> CountOp -> HostType t -> HostType t
countT I32IsInt op a = fromIntegral (countOp op a)
countT I64IsInt op a = fromIntegral (countOp op a)

countOp :: FiniteBits a => CountOp -> a -> Int
countOp OpClz = countLeadingZeros
countOp OpCtz = countTrailingZeros
countOp OpPopcnt = popCount

floatUnT :: IsFloat t -> FloatUnOp -> HostType t -> HostType t
floatUnT F32IsFloat op a = floatUnOp op a
floatUnT F64IsFloat op a = floatUnOp op a

floatUnOp :: RealFloat a => FloatUnOp -> a -> a
floatUnOp op a = case op of
    FAbs -> abs a
    FNeg -> negate a
    FSqrt -> sqrt a
    FCeil -> roundWith ceiling a
    FFloor -> roundWith floor a
    FTrunc -> roundWith truncate a
    FNearest -> roundWith round a -- Haskell's 'round' is ties-to-even, as the spec requires

{- | Round to an integral value the WebAssembly way: NaN and the infinities pass through, and a
  zero result keeps the sign of the input (@ceil -0.5 = -0@) — both of which a detour through
  'Integer' would lose.
-}
roundWith :: RealFloat a => (a -> Integer) -> a -> a
roundWith roundToInteger x
    | isNaN x || isInfinite x = x
    | rounded == 0 && (x < 0 || isNegativeZero x) = -0.0
    | otherwise = rounded
  where
    rounded = fromInteger (roundToInteger x)

floatBinT ::
    IsFloat t ->
    FloatBinOp ->
    HostType t ->
    HostType t ->
    HostType t
floatBinT F32IsFloat op = case op of
    FMin -> wasmMin
    FMax -> wasmMax
    FCopysign -> copysign32
floatBinT F64IsFloat op = case op of
    FMin -> wasmMin
    FMax -> wasmMax
    FCopysign -> copysign64

{- | Widen a loaded word to the access's integer type, sign- or zero-extending from the narrow
  width the witness names.
-}
narrowLoadT :: NarrowWidth t -> Signedness -> Word64 -> HostType t
narrowLoadT nw sign word = case narrowInt nw of
    I32IsInt -> fromIntegral (extendNarrow (narrowBytes nw) sign word)
    I64IsInt -> extendNarrow (narrowBytes nw) sign word

extendNarrow :: Int -> Signedness -> Word64 -> Word64
extendNarrow width sign raw =
    let bits = width * 8
     in if sign == Signed && testBit raw (bits - 1)
            then raw .|. (complement 0 `shiftL` bits)
            else raw

-- | The value as a word; the store keeps as many low bytes of it as the narrow width names.
narrowStoreT :: NarrowWidth t -> HostType t -> Word64
narrowStoreT nw value = case narrowInt nw of
    I32IsInt -> fromIntegral value
    I64IsInt -> value
