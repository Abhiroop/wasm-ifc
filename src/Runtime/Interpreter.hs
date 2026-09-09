{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

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
    spec-defined runtime errors (division by zero, out-of-bounds access, @unreachable@).

So progress reads: every well-typed configuration either steps, finishes, or traps.
-}
module Runtime.Interpreter (
    FuncInst (..),
    FuncInsts (..),
    getFunc,
    ModuleInst (..),
    Store (..),
    currentMem,
    storeMem,
    Config (..),
    Control (..),
    StepResult (..),
    HostRequest (..),
    Suspended (..),
    resumeWith,
    Halt (..),
    Outcome (..),
    step,
    run,
    runFunction,
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
import Data.Word (Word32, Word64, Word8)
import GHC.Float (castDoubleToWord64, castFloatToWord32, castWord32ToFloat, castWord64ToDouble)

import Data.List.Singletons (type (++))
import Runtime.Bytes (bytesOfWord32, bytesOfWord64, word32OfBytes, word64OfBytes)
import Runtime.Convert (convertVal)
import Runtime.Host (WasiFunc, wasiFuncType)
import Runtime.MemInst (MemInst, growMemory, memoryPages, readBytes, writeBytes)
import Runtime.Numeric (copysign32, copysign64, fromSigned32, fromSigned64, intDiv32, intDiv64, intRem32, intRem64, toSigned32, toSigned64, wasmMax, wasmMin)
import Runtime.Stack
import Runtime.Trap (Trap (..))
import Syntax.Immediates (HostType)
import Syntax.Instructions (
    BitwiseOp (..),
    CountOp (..),
    Expr (..),
    FloatBinOp (..),
    FloatUnOp (..),
    Instr (..),
 )
import Syntax.Types
import Validation.Reflect (appendNil)
import Validation.Shape (Append, Elem (..), FrameShape (..), ModuleFuncs, ModuleGlobals, ModuleMems, ModuleShape, ReverseOnto, appendFromSing)

-- *** Module and runtime state ***

{- | The type an 'Expr' must have to be a function body: from the empty operand stack it
  produces the function's results @rs@; its frame binds @locals@ and return type @rs@; and
  it runs under exactly one enclosing label — the function's own result — which is what
  @return@ and falling off the end both target.
-}
type FunctionBody mod locals rs = Expr mod ('FrameShape locals rs) '[rs] '[] rs

{- | A function instance: either a WebAssembly function — the zero-initialised values of the
  locals it declares, together with its body — or an imported host function. A body's locals
  are the parameters (local 0 is the first parameter, so the argument segment — last argument
  on top — is reversed onto them) followed by the declared locals. A host function can only
  live in a module that has a memory, which WASI requires; the constraint is packed here so
  the driver can reach that memory without asking.
-}
data FuncInst (mod :: ModuleShape) (ft :: FuncType) where
    WasmFunc ::
        -- | zero-inits for the declared (non-parameter) locals
        LocalInsts declared ->
        -- | the body, typed @'[] -> rs@
        FunctionBody mod (ReverseOnto ps declared) rs ->
        FuncInst mod ('FuncType ps rs)
    HostFunc :: (ModuleMems mod ~ (mem ': mems)) => WasiFunc ft -> FuncInst mod ft

-- | The functions of a module, one typed body per signature in 'ModuleFuncs'.
data FuncInsts (mod :: ModuleShape) (fts :: [FuncType]) where
    FsNil :: FuncInsts mod '[]
    FsCons :: FuncInst mod ft -> FuncInsts mod fts -> FuncInsts mod (ft ': fts)

getFunc :: Elem ft fts -> FuncInsts mod fts -> FuncInst mod ft
getFunc Here (FsCons f _) = f
getFunc (There ix) (FsCons _ rest) = getFunc ix rest

{- | The mutable part of the running state: the globals and memories that instructions update
  in place. (The WASM spec's store also holds tables, element and data segments; this
  implementation has none of those — no @call_indirect@ or bulk memory — and functions are
  immutable, so they are passed to 'step' read-only rather than kept here.)
-}
data Store (mod :: ModuleShape) = Store
    { stGlobals :: GlobalInsts (ModuleGlobals mod)
    , stMems :: MemInsts (ModuleMems mod)
    }

{- | A fully instantiated module: its function instances plus the initial globals and
  memories. (The runtime counterpart of a 'Syntax.Module.RawModule', per the
  description/shape/instance naming: @RawModule@ → 'Validation.Shape.ModuleShape' →
  'ModuleInst'.)
-}
data ModuleInst (mod :: ModuleShape) = ModuleInst
    { miFuncs :: FuncInsts mod (ModuleFuncs mod)
    , miGlobals :: GlobalInsts (ModuleGlobals mod)
    , miMems :: MemInsts (ModuleMems mod)
    }

{- *** The control stack ***

   'Control' is the runtime realisation of the type-level @labels@ environment: the stack of
   what to do when the running code finishes or a branch unwinds to it. Each entry is a block
   or @if@ label ('FLabel'), a @loop@ label ('FLoop'), a call boundary — the spec's
   /activation frame/ — ('FCall'), or the entry boundary ('FHalt'); each label a branch can
   target corresponds to one entry. It is indexed by

     * @res@    — the result of the whole computation (the entry function),
     * @ret@    — the result of the /current/ activation,
     * @locals@ and @labels@ — the locals and label environment of the running code,
     * @cur@    — the value stack the running code leaves when it falls through to this entry.

   An @Elem rs labels@ branch target therefore selects an entry directly, and unwinding it
   stays type-correct without any coercion.
-}
data
    Control
        (mod :: ModuleShape)
        (res :: ResultType)
        (ret :: ResultType)
        (locals :: [ValType])
        (labels :: [ResultType])
        (cur :: [ValType])
    where
    {- | The bottom of the stack: the entry activation. Falling through (or @br@ to its only
    label, or @return@) leaving @res@ completes the whole computation.
    -}
    FHalt :: Control mod res res locals '[res] res
    {- | A @block@/@if@ label. On normal completion or a branch to it, put the produced @rs@
    on top of the saved @below@ and run the continuation in the enclosing environment.
    -}
    FLabel ::
        ValueStack below ->
        Expr mod ('FrameShape locals ret) labels (rs ++ below) contOut ->
        Control mod res ret locals labels contOut ->
        Control mod res ret locals (rs ': labels) rs
    {- | A @loop@ label. A branch to it (carrying the loop's parameters) restarts the body;
    normal completion runs the continuation, exactly like 'FLabel'.
    -}
    FLoop ::
        ValueStack below ->
        Expr mod ('FrameShape locals ret) (ps ': labels) ps rs ->
        Expr mod ('FrameShape locals ret) labels (rs ++ below) contOut ->
        Control mod res ret locals labels contOut ->
        Control mod res ret locals (ps ': labels) rs
    {- | A call boundary: the callee's bottom frame. When the callee finishes (or returns),
    put its @rs@ results on the caller's saved stack and resume the caller.
    -}
    FCall ::
        ValueStack below ->
        LocalInsts callerLocals ->
        Expr mod ('FrameShape callerLocals callerRet) callerLabels (rs ++ below) contOut ->
        Control mod res callerRet callerLocals callerLabels contOut ->
        Control mod res rs calleeLocals '[rs] rs

{- | A machine configuration. The instruction sequence runs from @cur@ to @out@; the control
  stack expects exactly the @out@ it leaves. All shape indices are existential; only the
  module signature @mod@ and the overall result @res@ are visible.
-}
data Config (mod :: ModuleShape) (res :: ResultType) where
    Config ::
        Store mod ->
        LocalInsts locals ->
        ValueStack cur ->
        Expr mod ('FrameShape locals ret) labels cur out ->
        Control mod res ret locals labels out ->
        Config mod res

{- | The result of one 'step': a successor configuration; the final value stack together with
  the store as the computation left it; or a call into the host, which the pure machine
  cannot perform and so hands out as a request.
-}
data StepResult (mod :: ModuleShape) (res :: ResultType) where
    Stepped :: Config mod res -> StepResult mod res
    Done :: Store mod -> ValueStack res -> StepResult mod res
    HostCall :: HostRequest mod res -> StepResult mod res

{- | A call into the host, suspended: which function, its arguments (a stack of exactly its
  parameter shape), the store to perform it against, and how to continue once the results
  are known. The memory constraint travels with it so the driver can read and write memory.
-}
data HostRequest (mod :: ModuleShape) (res :: ResultType) where
    HostRequest ::
        (ModuleMems mod ~ (mem ': mems)) =>
        WasiFunc ('FuncType ps rs) ->
        ValueStack ps ->
        Store mod ->
        Suspended mod res rs ->
        HostRequest mod res

{- | A configuration with an @rs@-shaped hole where a call's results go: the caller's locals,
  the stack it saved below the arguments, the code after the call and its control stack. The
  'Append' witness says where the results sit on that stack.
-}
data Suspended (mod :: ModuleShape) (res :: ResultType) (rs :: ResultType) where
    Suspended ::
        Append rs below full ->
        LocalInsts locals ->
        ValueStack below ->
        Expr mod ('FrameShape locals ret) labels full contOut ->
        Control mod res ret locals labels contOut ->
        Suspended mod res rs

-- | Fill the hole: continue the suspended computation with the host's results and store.
resumeWith :: Store mod -> ValueStack rs -> Suspended mod res rs -> Config mod res
resumeWith store results (Suspended witness locals below cont control) =
    Config store locals (appendWith witness results below) cont control

-- *** The step relation ***

{- | Advance one configuration. Total over every well-typed configuration: see the module
  header for how this constitutes the progress half of type soundness.
-}
step :: FuncInsts mod (ModuleFuncs mod) -> Config mod res -> Either Trap (StepResult mod res)
step funcs (Config store locals stack code control) = case code of
    INil -> Right (popControl store locals stack control)
    instr :. rest -> case instr of
        {- Constants & numeric -}
        IConst _ literal -> stepped store locals (literal :# stack) rest control
        IAdd nt -> stepBin store locals stack (numBinary nt (+)) rest control
        ISub nt -> stepBin store locals stack (numBinary nt (-)) rest control
        IMul nt -> stepBin store locals stack (numBinary nt (*)) rest control
        IDiv sn -> case stack of
            b :# a :# r -> case numDiv sn a b of
                Right v -> stepped store locals (v :# r) rest control
                Left t -> Left t
        IRem nt sign -> case stack of
            b :# a :# r -> case numRem nt sign a b of
                Right v -> stepped store locals (v :# r) rest control
                Left t -> Left t
        {- Comparison -}
        IEqz nt -> stepUn store locals stack (numEqz nt) rest control
        IEq nt -> stepBin store locals stack (numEqNe (==) nt) rest control
        INe nt -> stepBin store locals stack (numEqNe (/=) nt) rest control
        ILt sn -> stepBin store locals stack (numCompare (<) sn) rest control
        IGt sn -> stepBin store locals stack (numCompare (>) sn) rest control
        ILe sn -> stepBin store locals stack (numCompare (<=) sn) rest control
        IGe sn -> stepBin store locals stack (numCompare (>=) sn) rest control
        {- Conversions -}
        IConvert op -> case stack of
            v :# r -> case convertVal op v of
                Right result -> stepped store locals (result :# r) rest control
                Left t -> Left t
        {- Integer bitwise / shift / count, floating-point unary / binary -}
        IBitwise nt op -> stepBin store locals stack (bitwiseT nt op) rest control
        ICount nt op -> stepUn store locals stack (countT nt op) rest control
        IFloatUn nt op -> stepUn store locals stack (floatUnT nt op) rest control
        IFloatBin nt op -> stepBin store locals stack (floatBinT nt op) rest control
        {- Memory size / grow & narrow access -}
        IMemSize -> stepped store locals (memoryPages (currentMem store) :# stack) rest control
        IMemGrow -> case stack of
            delta :# r ->
                let mem = currentMem store
                 in case growMemory delta mem of
                        Just grown -> stepped (storeMem grown store) locals (memoryPages mem :# r) rest control
                        Nothing -> stepped store locals (growFailed :# r) rest control
        ILoadN nw sign memArg -> case stack of
            addr :# r ->
                case readBytes (currentMem store) (effectiveAddr addr memArg) (narrowBytes nw) of
                    Just bytes -> stepped store locals (narrowLoadT nw sign bytes :# r) rest control
                    Nothing -> Left OutOfBoundsMemoryAccess
        IStoreN nw memArg -> case stack of
            value :# addr :# r ->
                case writeBytes (currentMem store) (effectiveAddr addr memArg) (narrowStoreT nw value) of
                    Just mem' -> stepped (storeMem mem' store) locals r rest control
                    Nothing -> Left OutOfBoundsMemoryAccess
        {- Stack management -}
        IDrop -> case stack of _ :# r -> stepped store locals r rest control
        ISelect _ -> case stack of
            cond :# second :# first :# r ->
                stepped store locals ((if cond /= 0 then first else second) :# r) rest control
        {- Locals & globals -}
        ILocalGet ix -> stepped store locals (getLocal ix locals :# stack) rest control
        ILocalSet ix -> case stack of v :# r -> stepped store (setLocal ix v locals) r rest control
        ILocalTee ix -> case stack of v :# _ -> stepped store (setLocal ix v locals) stack rest control
        IGlobalGet ix -> stepped store locals (getGlobal ix (store.stGlobals) :# stack) rest control
        IGlobalSet ix -> case stack of
            v :# r -> stepped store {stGlobals = setGlobal ix v (store.stGlobals)} locals r rest control
        {- Memory -}
        ILoad nt memArg -> case stack of
            addr :# r ->
                case readBytes (currentMem store) (effectiveAddr addr memArg) (numBytes nt) of
                    Just bytes -> stepped store locals (loadValue nt bytes :# r) rest control
                    Nothing -> Left OutOfBoundsMemoryAccess
        IStore nt memArg -> case stack of
            value :# addr :# r ->
                case writeBytes (currentMem store) (effectiveAddr addr memArg) (storeBytes nt value) of
                    Just mem' -> stepped (storeMem mem' store) locals r rest control
                    Nothing -> Left OutOfBoundsMemoryAccess
        {- Calls: push a call frame and start the callee over an empty stack — or, for a host
           function, hand the call out as a request with the caller suspended around it -}
        ICall witness ix -> case getFunc ix funcs of
            WasmFunc defaults body ->
                let (args, below) = splitStack witness stack
                    calleeLocals = reverseOnto args defaults
                 in Right (Stepped (Config store calleeLocals VNil body (FCall below locals rest control)))
            HostFunc wasiFunc -> case wasiFuncType wasiFunc of
                SFuncType _ resultsS ->
                    let (args, below) = splitStack witness stack
                        suspended = Suspended (appendFromSing resultsS) locals below rest control
                     in Right (HostCall (HostRequest wasiFunc args store suspended))
        {- Structured control: push the matching frame and run the body -}
        IBlock witness body ->
            let (params, below) = splitStack witness stack
             in Right (Stepped (Config store locals params body (FLabel below rest control)))
        ILoop witness body ->
            let (params, below) = splitStack witness stack
             in Right (Stepped (Config store locals params body (FLoop below body rest control)))
        IIf witness thenArm elseArm -> case stack of
            cond :# below' ->
                let (params, below) = splitStack witness below'
                    arm = if cond /= 0 then thenArm else elseArm
                 in Right (Stepped (Config store locals params arm (FLabel below rest control)))
        {- Branches: unwind the control stack to the targeted frame -}
        IBr witness ix -> let (vs, _) = splitStack witness stack in Right (unwind store locals ix vs control)
        IBrIf witness ix -> case stack of
            cond :# below'
                | cond /= 0 ->
                    let (vs, _) = splitStack witness below'
                     in Right (unwind store locals ix vs control)
                | otherwise -> stepped store locals below' rest control
        IBrTable witness targets def -> case stack of
            idx :# below' ->
                let target = case drop (fromIntegral idx) targets of t : _ -> t; [] -> def
                    (vs, _) = splitStack witness below'
                 in Right (unwind store locals target vs control)
        IReturn witness ->
            let (vs, _) = splitStack witness stack in Right (returnUnwind store locals vs control)
        {- Inert -}
        INop -> stepped store locals stack rest control
        IUnreachable -> Left UnreachableExecuted

-- | The "continue in the current frame" case: wrap a successor configuration.
stepped ::
    Store mod ->
    LocalInsts locals ->
    ValueStack si ->
    Expr mod ('FrameShape locals ret) labels si out ->
    Control mod res ret locals labels out ->
    Either Trap (StepResult mod res)
stepped store locals stack code control = Right (Stepped (Config store locals stack code control))

-- | Pop two same-typed operands (@a@ below, @b@ on top), push @op a b@, and continue.
stepBin ::
    Store mod ->
    LocalInsts locals ->
    ValueStack (x ': x ': s) ->
    (HostType x -> HostType x -> HostType z) ->
    Expr mod ('FrameShape locals ret) labels (z ': s) out ->
    Control mod res ret locals labels out ->
    Either Trap (StepResult mod res)
stepBin store locals (b :# a :# r) op = stepped store locals (op a b :# r)

-- | Pop one operand, push @op a@, and continue.
stepUn ::
    Store mod ->
    LocalInsts locals ->
    ValueStack (x ': s) ->
    (HostType x -> HostType z) ->
    Expr mod ('FrameShape locals ret) labels (z ': s) out ->
    Control mod res ret locals labels out ->
    Either Trap (StepResult mod res)
stepUn store locals (a :# r) op = stepped store locals (op a :# r)

{- | The module's single memory, and a store update for it. The @ModuleMems mod ~ (m ': ms)@
  constraint every memory instruction carries makes both total.
-}
currentMem :: (ModuleMems mod ~ (m ': ms)) => Store mod -> MemInst m
currentMem store = firstMem store.stMems

storeMem :: (ModuleMems mod ~ (m ': ms)) => MemInst m -> Store mod -> Store mod
storeMem mem store = store {stMems = setFirstMem mem store.stMems}

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
    LocalInsts locals ->
    ValueStack rs ->
    ValueStack below ->
    Expr mod ('FrameShape locals ret) labels (rs ++ below) contOut ->
    Control mod res ret locals labels contOut ->
    StepResult mod res
resume store locals vs below cont rest = Stepped (Config store locals (appendStack vs below) cont rest)

-- | The current sequence reached its end (left @cur@): hand control to the top frame.
popControl ::
    Store mod ->
    LocalInsts locals ->
    ValueStack cur ->
    Control mod res ret locals labels cur ->
    StepResult mod res
popControl store _ vs FHalt = Done store vs
popControl store locals vs (FLabel below cont rest) = resume store locals vs below cont rest
popControl store locals vs (FLoop below _ cont rest) = resume store locals vs below cont rest
popControl store _ vs (FCall below cl cont cf) = resume store cl vs below cont cf

{- | Unwind to the @ix@-th enclosing label, carrying that label's values. A block/if label
  resumes after the construct; a loop label restarts the body; the function's own label
  returns from it.
-}
unwind ::
    Store mod ->
    LocalInsts locals ->
    Elem rs labels ->
    ValueStack rs ->
    Control mod res ret locals labels cur ->
    StepResult mod res
unwind store _ Here vs FHalt = Done store vs
unwind store locals Here vs (FLabel below cont rest) = resume store locals vs below cont rest
unwind store locals Here vs (FLoop below body cont rest) =
    Stepped (Config store locals vs body (FLoop below body cont rest))
unwind store _ Here vs (FCall below cl cont cf) = resume store cl vs below cont cf
unwind store locals (There ix') vs (FLabel _ _ rest) = unwind store locals ix' vs rest
unwind store locals (There ix') vs (FLoop _ _ _ rest) = unwind store locals ix' vs rest
unwind _ _ (There ix') _ (FCall {}) = case ix' of {}
unwind _ _ (There ix') _ FHalt = case ix' of {}

-- | @return@: unwind past every label frame in the current activation to the call boundary.
returnUnwind ::
    Store mod ->
    LocalInsts locals ->
    ValueStack ret ->
    Control mod res ret locals labels cur ->
    StepResult mod res
returnUnwind store _ vs FHalt = Done store vs
returnUnwind store _ vs (FCall below cl cont cf) = resume store cl vs below cont cf
returnUnwind store locals vs (FLabel _ _ rest) = returnUnwind store locals vs rest
returnUnwind store locals vs (FLoop _ _ _ rest) = returnUnwind store locals vs rest

-- | Where a run stops: with its results and final store, or waiting for the host.
data Halt (mod :: ModuleShape) (res :: ResultType) where
    Finished :: Store mod -> ValueStack res -> Halt mod res
    AwaitingHost :: HostRequest mod res -> Halt mod res

{- | Iterate 'step' until the computation finishes or needs the host. (This is the only partial
  function here — it loops, which is termination, a property orthogonal to the progress and
  preservation that 'step' carries.)
-}
run :: FuncInsts mod (ModuleFuncs mod) -> Config mod res -> Either Trap (Halt mod res)
run funcs config = case step funcs config of
    Left t -> Left t
    Right (Done store vs) -> Right (Finished store vs)
    Right (HostCall request) -> Right (AwaitingHost request)
    Right (Stepped next) -> run funcs next

-- | How a function invocation ends: with the module as the call left it, or needing the host.
data Outcome (mod :: ModuleShape) (rs :: ResultType) where
    Completed :: ModuleInst mod -> ValueStack rs -> Outcome mod rs
    NeedsHost :: HostRequest mod rs -> Outcome mod rs

{- | Run a function against an instantiated module: seed the entry activation and iterate.
  The module comes back with its globals and memories as the call left them, so state
  persists from one invocation to the next; on a trap the caller keeps the module it had.
  Calling a host function directly (an exported import) is a request straight away.
-}
runFunction ::
    ModuleInst mod ->
    FuncInst mod ('FuncType ps rs) ->
    ValueStack ps ->
    Either Trap (Outcome mod rs)
runFunction tm (WasmFunc defaults body) args = do
    halt <- run (tm.miFuncs) (Config store locals VNil body FHalt)
    Right $ case halt of
        Finished store' results -> Completed tm {miGlobals = store'.stGlobals, miMems = store'.stMems} results
        AwaitingHost request -> NeedsHost request
  where
    store = Store (tm.miGlobals) (tm.miMems)
    locals = reverseOnto args defaults
runFunction tm (HostFunc wasiFunc) args = case wasiFuncType wasiFunc of
    SFuncType _ resultsS ->
        Right (NeedsHost (HostRequest wasiFunc args (Store (tm.miGlobals) (tm.miMems)) (Suspended (appendNil resultsS) LNil VNil INil FHalt)))

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

loadValue :: IsNum t -> [Word8] -> HostType t
loadValue I32IsNum = word32OfBytes
loadValue I64IsNum = word64OfBytes
loadValue F32IsNum = castWord32ToFloat . word32OfBytes
loadValue F64IsNum = castWord64ToDouble . word64OfBytes

storeBytes :: IsNum t -> HostType t -> [Word8]
storeBytes I32IsNum = bytesOfWord32
storeBytes I64IsNum = bytesOfWord64
storeBytes F32IsNum = bytesOfWord32 . castFloatToWord32
storeBytes F64IsNum = bytesOfWord64 . castDoubleToWord64

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

{- | Widen loaded bytes to the access's integer type, sign- or zero-extending from the narrow
  width the witness names.
-}
narrowLoadT :: NarrowWidth t -> Signedness -> [Word8] -> HostType t
narrowLoadT nw sign bytes = case narrowInt nw of
    I32IsInt -> fromIntegral (assembleNarrow (narrowBytes nw) sign bytes)
    I64IsInt -> assembleNarrow (narrowBytes nw) sign bytes

assembleNarrow :: Int -> Signedness -> [Word8] -> Word64
assembleNarrow width sign bytes =
    let raw = foldr (.|.) 0 [fromIntegral b `shiftL` (8 * i) | (i, b) <- zip [0 ..] bytes] :: Word64
        bits = width * 8
     in if sign == Signed && testBit raw (bits - 1)
            then raw .|. (complement 0 `shiftL` bits)
            else raw

-- | The low bytes of the value, as many as the narrow width names.
narrowStoreT :: NarrowWidth t -> HostType t -> [Word8]
narrowStoreT nw value = case narrowInt nw of
    I32IsInt -> take (narrowBytes nw) (bytesOfWord64 (fromIntegral value))
    I64IsInt -> take (narrowBytes nw) (bytesOfWord64 value)
