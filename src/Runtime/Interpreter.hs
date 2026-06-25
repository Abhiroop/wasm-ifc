{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

-- | The intrinsically-typed interpreter, as a small-step abstract machine.
--
-- A 'Config' is a machine configuration: the mutable store, the active frame's locals, the
-- current value stack, the instruction sequence left to run, and a 'Frames' control stack
-- of what to do when the current sequence finishes or a branch unwinds to it. 'step'
-- advances one configuration; 'run' iterates it.
--
-- The point of this shape (rather than a recursive big-step evaluator) is that it /is/ the
-- type-soundness argument:
--
--   * Preservation is by construction — 'Config' and 'Frames' are indexed so only
--     well-typed configurations are representable, and 'step' produces another 'Config'.
--   * Progress is the totality of 'step' — it is defined on every non-final configuration,
--     with no @error@ and no incomplete pattern (the index of each instruction guarantees
--     the operands it needs are present, and the GADTs make every dispatch exhaustive).
--   * A 'Trap' is a defined result, not a stuck state: 'step' may return @Left trap@ for the
--     spec-defined runtime errors (division by zero, out-of-bounds access, @unreachable@).
--
-- So progress reads: every well-typed configuration either steps, finishes, or traps.
module Runtime.Interpreter
    ( FuncInst (..)
    , FuncInsts (..)
    , getFunc
    , ModuleInst (..)
    , Store (..)
    , Config (..)
    , Frames (..)
    , StepResult (..)
    , step
    , run
    , runFunction
    ) where

import Data.Bits   (FiniteBits, complement, countLeadingZeros, countTrailingZeros, popCount,
                    rotateL, rotateR, shiftL, shiftR, testBit, xor, (.&.), (.|.))
import Data.Word   (Word8, Word32, Word64)
import GHC.Float   (castDoubleToWord64, castFloatToWord32, castWord32ToFloat, castWord64ToDouble)

import Runtime.Bytes   (bytesOfWord32, bytesOfWord64, word32OfBytes, word64OfBytes)
import Runtime.Convert (convertVal)
import Runtime.Numeric (copysign, intDiv32, intDiv64, intRem32, intRem64, wasmMax, wasmMin)
import Runtime.MemInst   (MemInst, growMemory, memoryPages, readBytes, writeBytes)
import Runtime.Trap    (Trap (..))
import Runtime.Values  (RuntimeHostType, Val, fromF32, fromF64, fromI32, fromI64, fromSigned32,
                       fromSigned64, toF32, toF64, toI32, toI64, toSigned32, toSigned64)
import Syntax.Types
import Validation.Shape   (ModuleFuncs, ModuleGlobals, ModuleMems, Elem (..), ModuleShape, type (++))
import Syntax.Instructions (Instr (..), Expr (..), BitwiseOp (..), CountOp (..),
                           FloatUnOp (..), FloatBinOp (..))
import Runtime.Stack

{- *** Module and runtime state *** -}

-- | A function instance: its body together with the zero-initialised values of the locals it
--   declares. The body runs over an empty operand stack, with the declared locals
--   (parameters followed by those zero-inits) and a single enclosing label — the result
--   type — so that @return@ and falling off the end agree.
--- XXX: use better variable names so that this reads way nicer. For example, what is "Expr shape rs (ps ++ localDecls) '[rs] '[] rs" even saying? If variables had more specific and longer names, leveraged record syntax where possible, etc., it could be possible to make it closer to English (I know miracles don't exist and it will never read like English, but it could be better)
data FuncInst (shape :: ModuleShape) (ft :: FuncType) where
    FuncInst :: LocalInsts localDecls   -- ^ default values for the declared (non-parameter) locals
         -> Expr shape rs (ps ++ localDecls) '[rs] '[] rs
         -> FuncInst shape ('FuncType ps rs)

-- | The functions of a module, one typed body per signature in 'ModuleFuncs'.
data FuncInsts (shape :: ModuleShape) (fts :: [FuncType]) where
    FsNil  :: FuncInsts shape '[]
    FsCons :: FuncInst shape ft -> FuncInsts shape fts -> FuncInsts shape (ft ': fts)

getFunc :: Elem ft fts -> FuncInsts shape fts -> FuncInst shape ft
getFunc Here       (FsCons f _)    = f
getFunc (There ix) (FsCons _ rest) = getFunc ix rest

-- | The mutable part of the running state: the globals and memories that instructions update
--   in place. (The WASM spec's store also holds tables, element and data segments; this
--   implementation has none of those — no @call_indirect@ or bulk memory — and functions are
--   immutable, so they are passed to 'step' read-only rather than kept here.)
data Store (shape :: ModuleShape) = Store
    { stGlobals :: GlobalInsts (ModuleGlobals shape)
    , stMems    :: MemInsts (ModuleMems shape)
    }

-- | A fully instantiated module: its function instances plus the initial globals and
--   memories. (The runtime counterpart of a 'Syntax.Module.RawModule', per the
--   description/shape/instance naming: @RawModule@ → 'Validation.Shape.ModuleShape' →
--   'ModuleInst'.)
data ModuleInst (shape :: ModuleShape) = ModuleInst
    { miFuncs   :: FuncInsts shape (ModuleFuncs shape)
    , miGlobals :: GlobalInsts (ModuleGlobals shape)
    , miMems    :: MemInsts (ModuleMems shape)
    }

{- *** The control stack ***

   'Frames' is the runtime realisation of the type-level @labels@ environment: each label a
   branch can target corresponds to one frame. It is indexed by

     * @res@    — the result of the whole computation (the entry function),
     * @ret@    — the result of the /current/ activation,
     * @locals@ and @labels@ — the locals and label environment of the running code,
     * @cur@    — the value stack the running code leaves when it falls through to this frame.

   An @Elem rs labels@ branch target therefore selects a frame directly, and unwinding it
   stays type-correct without any coercion. -}
data Frames (shape :: ModuleShape) (res :: [ValType]) (ret :: [ValType])
            (locals :: [ValType]) (labels :: [[ValType]]) (cur :: [ValType]) where
    -- | The bottom of the stack: the entry activation. Falling through (or @br@ to its only
    --   label, or @return@) leaving @res@ completes the whole computation.
    FHalt :: Frames shape res res locals '[res] res

    -- | A @block@/@if@ label. On normal completion or a branch to it, put the produced @rs@
    --   on top of the saved @below@ and run the continuation in the enclosing environment.
    FLabel :: ValueStack below
           -> Expr shape ret locals labels (rs ++ below) contOut
           -> Frames shape res ret locals labels contOut
           -> Frames shape res ret locals (rs ': labels) rs

    -- | A @loop@ label. A branch to it (carrying the loop's parameters) restarts the body;
    --   normal completion runs the continuation, exactly like 'FLabel'.
    FLoop :: ValueStack below
          -> Expr shape ret locals (ps ': labels) ps rs
          -> Expr shape ret locals labels (rs ++ below) contOut
          -> Frames shape res ret locals labels contOut
          -> Frames shape res ret locals (ps ': labels) rs

    -- | A call boundary: the callee's bottom frame. When the callee finishes (or returns),
    --   put its @rs@ results on the caller's saved stack and resume the caller.
    FCall :: ValueStack below
          -> LocalInsts callerLocals
          -> Expr shape callerRet callerLocals callerLabels (rs ++ below) contOut
          -> Frames shape res callerRet callerLocals callerLabels contOut
          -> Frames shape res rs calleeLocals '[rs] rs

-- | A machine configuration. The instruction sequence runs from @cur@ to @out@; the control
--   stack expects exactly the @out@ it leaves. All shape indices are existential; only the
--   module signature @shape@ and the overall result @res@ are visible.
data Config (shape :: ModuleShape) (res :: [ValType]) where
    Config :: Store shape
           -> LocalInsts locals
           -> ValueStack cur
           -> Expr shape ret locals labels cur out
           -> Frames shape res ret locals labels out
           -> Config shape res

-- | The result of one 'step': either a successor configuration, or the final value stack.
data StepResult (shape :: ModuleShape) (res :: [ValType]) where
    Stepped :: Config shape res -> StepResult shape res
    Done    :: ValueStack res -> StepResult shape res

{- *** The step relation *** -}

-- | Advance one configuration. Total over every well-typed configuration: see the module
--   header for how this constitutes the progress half of type soundness.
step ::FuncInsts shape (ModuleFuncs shape) -> Config shape res -> Either Trap (StepResult shape res)
step funcs (Config store locals stack code frames) = case code of
    INil          -> Right (popFrame store locals stack frames)
    instr :. rest -> case instr of
        {- Constants & numeric -}
        IConst _ literal -> stepped store locals (literal :# stack) rest frames
        IAdd nt -> stepBin store locals stack (numBinary nt (+)) rest frames
        ISub nt -> stepBin store locals stack (numBinary nt (-)) rest frames
        IMul nt -> stepBin store locals stack (numBinary nt (*)) rest frames
        IDiv nt sign -> case stack of
            b :# a :# r -> case numDiv nt sign a b of
                Right v -> stepped store locals (v :# r) rest frames
                Left t  -> Left t
        IRem nt sign -> case stack of
            b :# a :# r -> case numRem nt sign a b of
                Right v -> stepped store locals (v :# r) rest frames
                Left t  -> Left t

        {- Comparison -}
        IEqz nt      -> stepUn  store locals stack (numEqz nt) rest frames
        IEq  nt      -> stepBin store locals stack (numCompare (==) nt Unsigned) rest frames
        INe  nt      -> stepBin store locals stack (numCompare (/=) nt Unsigned) rest frames
        ILt  nt sign -> stepBin store locals stack (numCompare (<)  nt sign) rest frames
        IGt  nt sign -> stepBin store locals stack (numCompare (>)  nt sign) rest frames
        ILe  nt sign -> stepBin store locals stack (numCompare (<=) nt sign) rest frames
        IGe  nt sign -> stepBin store locals stack (numCompare (>=) nt sign) rest frames

        {- Conversions -}
        IConvert from to op -> case stack of
            v :# r -> case convertVal op (toVal from v) of
                Right result -> stepped store locals (fromVal to result :# r) rest frames
                Left t       -> Left t

        {- Integer bitwise / shift / count, floating-point unary / binary -}
        IBitwise  nt op -> stepBin store locals stack (bitwiseT nt op) rest frames
        ICount    nt op -> stepUn  store locals stack (countT nt op) rest frames
        IFloatUn  nt op -> stepUn  store locals stack (floatUnT nt op) rest frames
        IFloatBin nt op -> stepBin store locals stack (floatBinT nt op) rest frames

        {- Memory size / grow & narrow access -}
        IMemSize -> stepped store locals (memoryPages (currentMem store) :# stack) rest frames
        IMemGrow -> case stack of
            delta :# r ->
                let mem = currentMem store
                in stepped (storeMem (growMemory delta mem) store) locals (memoryPages mem :# r) rest frames
        ILoadN nt width sign memArg -> case stack of
            addr :# r ->
                case readBytes (currentMem store) (addr + offset memArg) width of
                    Just bytes -> stepped store locals (narrowLoadT nt width sign bytes :# r) rest frames
                    Nothing    -> Left OutOfBoundsMemoryAccess
        IStoreN nt width memArg -> case stack of
            value :# addr :# r ->
                case writeBytes (currentMem store) (addr + offset memArg) (narrowStoreT nt width value) of
                    Just mem' -> stepped (storeMem mem' store) locals r rest frames
                    Nothing   -> Left OutOfBoundsMemoryAccess

        {- Stack management -}
        IDrop   -> case stack of _ :# r -> stepped store locals r rest frames
        ISelect -> case stack of
            cond :# a :# b :# r -> stepped store locals ((if cond /= 0 then a else b) :# r) rest frames

        {- Locals & globals -}
        ILocalGet ix  -> stepped store locals (getLocal ix locals :# stack) rest frames
        ILocalSet ix  -> case stack of v :# r -> stepped store (setLocal ix v locals) r rest frames
        ILocalTee ix  -> case stack of v :# _ -> stepped store (setLocal ix v locals) stack rest frames
        IGlobalGet ix -> stepped store locals (getGlobal ix (stGlobals store) :# stack) rest frames
        IGlobalSet ix -> case stack of
            v :# r -> stepped store { stGlobals = setGlobal ix v (stGlobals store) } locals r rest frames

        {- Memory -}
        ILoad nt memArg -> case stack of
            addr :# r ->
                case readBytes (currentMem store) (addr + offset memArg) (byteWidth nt) of
                    Just bytes -> stepped store locals (loadValue nt bytes :# r) rest frames
                    Nothing    -> Left OutOfBoundsMemoryAccess
        IStore nt memArg -> case stack of
            value :# addr :# r ->
                case writeBytes (currentMem store) (addr + offset memArg) (storeBytes nt value) of
                    Just mem' -> stepped (storeMem mem' store) locals r rest frames
                    Nothing   -> Left OutOfBoundsMemoryAccess

        {- Calls: push a call frame and start the callee over an empty stack -}
        ICall witness ix -> case getFunc ix funcs of
            FuncInst defaults body ->
                let (args, below) = splitStack witness stack
                    calleeLocals  = appendLocals (stackToLocals args) defaults
                in Right (Stepped (Config store calleeLocals VNil body (FCall below locals rest frames)))

        {- Structured control: push the matching frame and run the body -}
        IBlock witness body ->
            let (params, below) = splitStack witness stack
            in Right (Stepped (Config store locals params body (FLabel below rest frames)))
        ILoop witness body ->
            let (params, below) = splitStack witness stack
            in Right (Stepped (Config store locals params body (FLoop below body rest frames)))
        IIf witness thenArm elseArm -> case stack of
            cond :# below' ->
                let (params, below) = splitStack witness below'
                    arm = if cond /= 0 then thenArm else elseArm
                in Right (Stepped (Config store locals params arm (FLabel below rest frames)))

        {- Branches: unwind the control stack to the targeted frame -}
        IBr witness ix -> let (vs, _) = splitStack witness stack in Right (unwind store locals ix vs frames)
        IBrIf witness ix -> case stack of
            cond :# below'
                | cond /= 0 -> let (vs, _) = splitStack witness below'
                               in Right (unwind store locals ix vs frames)
                | otherwise -> stepped store locals below' rest frames
        IBrTable witness targets def -> case stack of
            idx :# below' ->
                let target  = if fromIntegral idx < length targets then targets !! fromIntegral idx else def
                    (vs, _) = splitStack witness below'
                in Right (unwind store locals target vs frames)
        IReturn witness ->
            let (vs, _) = splitStack witness stack in Right (returnUnwind store locals vs frames)

        {- Inert -}
        INop         -> stepped store locals stack rest frames
        IUnreachable -> Left UnreachableExecuted

-- | The "continue in the current frame" case: wrap a successor configuration.
stepped :: Store shape -> LocalInsts locals -> ValueStack si
        -> Expr shape ret locals labels si out -> Frames shape res ret locals labels out
        -> Either Trap (StepResult shape res)
stepped store locals stack code frames = Right (Stepped (Config store locals stack code frames))

-- | Pop two same-typed operands (@a@ below, @b@ on top), push @op a b@, and continue.
stepBin :: Store shape -> LocalInsts locals -> ValueStack (x ': x ': s)
        -> (RuntimeHostType x -> RuntimeHostType x -> RuntimeHostType z)
        -> Expr shape ret locals labels (z ': s) out -> Frames shape res ret locals labels out
        -> Either Trap (StepResult shape res)
stepBin store locals (b :# a :# r) op = stepped store locals (op a b :# r)

-- | Pop one operand, push @op a@, and continue.
stepUn :: Store shape -> LocalInsts locals -> ValueStack (x ': s)
       -> (RuntimeHostType x -> RuntimeHostType z)
       -> Expr shape ret locals labels (z ': s) out -> Frames shape res ret locals labels out
       -> Either Trap (StepResult shape res)
stepUn store locals (a :# r) op = stepped store locals (op a :# r)

-- | The module's single memory, and a store update for it. The @ModuleMems shape ~ (m ': ms)@
--   constraint every memory instruction carries makes both total.
currentMem :: (ModuleMems shape ~ (m ': ms)) => Store shape -> MemInst m
currentMem = firstMem . stMems

storeMem :: (ModuleMems shape ~ (m ': ms)) => MemInst m -> Store shape -> Store shape
storeMem mem store = store { stMems = setFirstMem mem (stMems store) }

-- | Resume the enclosing computation: put the produced values @vs@ on top of the frame's
--   saved @below@ stack and run its continuation. Shared by every frame that completes.
resume :: Store shape -> LocalInsts locals -> ValueStack rs -> ValueStack below
       -> Expr shape ret locals labels (rs ++ below) contOut
       -> Frames shape res ret locals labels contOut -> StepResult shape res
resume store locals vs below cont rest = Stepped (Config store locals (appendStack vs below) cont rest)

-- | The current sequence reached its end (left @cur@): hand control to the top frame.
popFrame :: Store shape -> LocalInsts locals -> ValueStack cur
         -> Frames shape res ret locals labels cur -> StepResult shape res
popFrame _     _      vs FHalt                      = Done vs
popFrame store locals vs (FLabel below cont rest)   = resume store locals vs below cont rest
popFrame store locals vs (FLoop below _ cont rest)  = resume store locals vs below cont rest
popFrame store _      vs (FCall below cl cont cf)    = resume store cl vs below cont cf

-- | Unwind to the @ix@-th enclosing label, carrying that label's values. A block/if label
--   resumes after the construct; a loop label restarts the body; the function's own label
--   returns from it.
unwind :: Store shape -> LocalInsts locals -> Elem rs labels -> ValueStack rs
       -> Frames shape res ret locals labels cur -> StepResult shape res
unwind _     _      Here        vs FHalt                     = Done vs
unwind store locals Here        vs (FLabel below cont rest)  = resume store locals vs below cont rest
unwind store locals Here        vs (FLoop below body cont rest) =
    Stepped (Config store locals vs body (FLoop below body cont rest))
unwind store _      Here        vs (FCall below cl cont cf)  = resume store cl vs below cont cf
unwind store locals (There ix') vs (FLabel _ _ rest)        = unwind store locals ix' vs rest
unwind store locals (There ix') vs (FLoop _ _ _ rest)       = unwind store locals ix' vs rest
unwind _     _      (There ix') _  (FCall {})               = case ix' of {}
unwind _     _      (There ix') _  FHalt                    = case ix' of {}

-- | @return@: unwind past every label frame in the current activation to the call boundary.
returnUnwind :: Store shape -> LocalInsts locals -> ValueStack ret
             -> Frames shape res ret locals labels cur -> StepResult shape res
returnUnwind _     _      vs FHalt                    = Done vs
returnUnwind store _      vs (FCall below cl cont cf) = resume store cl vs below cont cf
returnUnwind store locals vs (FLabel _ _ rest)       = returnUnwind store locals vs rest
returnUnwind store locals vs (FLoop _ _ _ rest)      = returnUnwind store locals vs rest

-- | Iterate 'step' to completion. (This is the only partial function here — it loops, which
--   is termination, a property orthogonal to the progress/preservation that 'step' carries.)
run :: FuncInsts shape (ModuleFuncs shape) -> Config shape res -> Either Trap (ValueStack res)
run funcs config = case step funcs config of
    Left t                -> Left t
    Right (Done vs)       -> Right vs
    Right (Stepped next)  -> run funcs next

-- | Run a function against an instantiated module: seed the entry activation and iterate.
runFunction :: ModuleInst shape -> FuncInst shape ('FuncType ps rs) -> ValueStack ps
            -> Either Trap (ValueStack rs)
runFunction tm (FuncInst defaults body) args =
    run (miFuncs tm) (Config store locals VNil body FHalt)
  where
    store  = Store (miGlobals tm) (miMems tm)
    locals = appendLocals (stackToLocals args) defaults

{- *** Numeric dispatch ***

   Each helper dispatches on the singleton (or integer/float witness) the instruction
   carries; matching it refines @RuntimeHostType ('Num t)@ to a concrete host type, so the
   operation is total over exactly the cases that can occur. -}

numBinary :: SNumType t
          -> (forall a. Num a => a -> a -> a)
          -> RuntimeHostType ('Num t) -> RuntimeHostType ('Num t) -> RuntimeHostType ('Num t)
numBinary SI32 op a b = op a b
numBinary SI64 op a b = op a b
numBinary SF32 op a b = op a b
numBinary SF64 op a b = op a b

numDiv :: SNumType t -> Signedness
       -> RuntimeHostType ('Num t) -> RuntimeHostType ('Num t) -> Either Trap (RuntimeHostType ('Num t))
numDiv SI32 sign a b = intDiv32 sign a b
numDiv SI64 sign a b = intDiv64 sign a b
numDiv SF32 _    a b = Right (a / b)
numDiv SF64 _    a b = Right (a / b)

numRem :: IsInt t -> Signedness
       -> RuntimeHostType ('Num t) -> RuntimeHostType ('Num t) -> Either Trap (RuntimeHostType ('Num t))
numRem IntI32 sign a b = intRem32 sign a b
numRem IntI64 sign a b = intRem64 sign a b

numCompare :: (forall a. Ord a => a -> a -> Bool) -> SNumType t -> Signedness
           -> RuntimeHostType ('Num t) -> RuntimeHostType ('Num t) -> RuntimeHostType ('Num 'I32)
numCompare cmp SI32 Signed   a b = boolWord (cmp (toSigned32 a) (toSigned32 b))
numCompare cmp SI32 Unsigned a b = boolWord (cmp a b)
numCompare cmp SI64 Signed   a b = boolWord (cmp (toSigned64 a) (toSigned64 b))
numCompare cmp SI64 Unsigned a b = boolWord (cmp a b)
numCompare cmp SF32 _        a b = boolWord (cmp a b)
numCompare cmp SF64 _        a b = boolWord (cmp a b)

numEqz :: SNumType t -> RuntimeHostType ('Num t) -> RuntimeHostType ('Num 'I32)
numEqz SI32 a = boolWord (a == 0)
numEqz SI64 a = boolWord (a == 0)
numEqz SF32 a = boolWord (a == 0)
numEqz SF64 a = boolWord (a == 0)

boolWord :: Bool -> Word32
boolWord True  = 1
boolWord False = 0

{- *** Memory <-> value marshalling *** -}

byteWidth :: SNumType t -> Int
byteWidth SI32 = 4
byteWidth SF32 = 4
byteWidth SI64 = 8
byteWidth SF64 = 8

loadValue :: SNumType t -> [Word8] -> RuntimeHostType ('Num t)
loadValue SI32 = word32OfBytes
loadValue SI64 = word64OfBytes
loadValue SF32 = castWord32ToFloat . word32OfBytes
loadValue SF64 = castWord64ToDouble . word64OfBytes

storeBytes :: SNumType t -> RuntimeHostType ('Num t) -> [Word8]
storeBytes SI32 = bytesOfWord32
storeBytes SI64 = bytesOfWord64
storeBytes SF32 = bytesOfWord32 . castFloatToWord32
storeBytes SF64 = bytesOfWord64 . castDoubleToWord64

{- *** Bitwise / count / float / narrow-memory helpers *** -}

bitwiseT :: IsInt t -> BitwiseOp
         -> RuntimeHostType ('Num t) -> RuntimeHostType ('Num t) -> RuntimeHostType ('Num t)
bitwiseT IntI32 op a b = bitwise32 op a b
bitwiseT IntI64 op a b = bitwise64 op a b

bitwise32 :: BitwiseOp -> Word32 -> Word32 -> Word32
bitwise32 op a b = case op of
    BwAnd          -> a .&. b
    BwOr           -> a .|. b
    BwXor          -> a `xor` b
    BwShl          -> a `shiftL` modBits 32 b
    BwShr Unsigned -> a `shiftR` modBits 32 b
    BwShr Signed   -> fromSigned32 (toSigned32 a `shiftR` modBits 32 b)
    BwRotl         -> rotateL a (modBits 32 b)
    BwRotr         -> rotateR a (modBits 32 b)

bitwise64 :: BitwiseOp -> Word64 -> Word64 -> Word64
bitwise64 op a b = case op of
    BwAnd          -> a .&. b
    BwOr           -> a .|. b
    BwXor          -> a `xor` b
    BwShl          -> a `shiftL` modBits 64 b
    BwShr Unsigned -> a `shiftR` modBits 64 b
    BwShr Signed   -> fromSigned64 (toSigned64 a `shiftR` modBits 64 b)
    BwRotl         -> rotateL a (modBits 64 b)
    BwRotr         -> rotateR a (modBits 64 b)

modBits :: Integral a => Int -> a -> Int
modBits width n = fromIntegral n `mod` width

countT :: IsInt t -> CountOp -> RuntimeHostType ('Num t) -> RuntimeHostType ('Num t)
countT IntI32 op a = fromIntegral (countOp op a)
countT IntI64 op a = fromIntegral (countOp op a)

countOp :: FiniteBits a => CountOp -> a -> Int
countOp OpClz    = countLeadingZeros
countOp OpCtz    = countTrailingZeros
countOp OpPopcnt = popCount

floatUnT :: IsFloat t -> FloatUnOp -> RuntimeHostType ('Num t) -> RuntimeHostType ('Num t)
floatUnT FloatF32 op a = floatUnOp op a
floatUnT FloatF64 op a = floatUnOp op a

floatUnOp :: RealFloat a => FloatUnOp -> a -> a
floatUnOp op a = case op of
    FAbs     -> abs a
    FNeg     -> negate a
    FSqrt    -> sqrt a
    FCeil    -> fromInteger (ceiling a)
    FFloor   -> fromInteger (floor a)
    FTrunc   -> fromInteger (truncate a)
    FNearest -> fromInteger (round a)

floatBinT :: IsFloat t -> FloatBinOp
          -> RuntimeHostType ('Num t) -> RuntimeHostType ('Num t) -> RuntimeHostType ('Num t)
floatBinT FloatF32 op a b = floatBinOp op a b
floatBinT FloatF64 op a b = floatBinOp op a b

floatBinOp :: RealFloat a => FloatBinOp -> a -> a -> a
floatBinOp FMin      = wasmMin
floatBinOp FMax      = wasmMax
floatBinOp FCopysign = copysign

narrowLoadT :: IsInt t -> Int -> Signedness -> [Word8] -> RuntimeHostType ('Num t)
narrowLoadT IntI32 width sign bytes = fromIntegral (assembleNarrow width sign bytes)
narrowLoadT IntI64 width sign bytes = assembleNarrow width sign bytes

assembleNarrow :: Int -> Signedness -> [Word8] -> Word64
assembleNarrow width sign bytes =
    let raw = foldr (.|.) 0 [fromIntegral b `shiftL` (8 * i) | (i, b) <- zip [0 ..] bytes] :: Word64
        bits = width * 8
    in if sign == Signed && testBit raw (bits - 1)
        then raw .|. (complement 0 `shiftL` bits)
        else raw

narrowStoreT :: IsInt t -> Int -> RuntimeHostType ('Num t) -> [Word8]
narrowStoreT IntI32 width value = take width (bytesOfWord64 (fromIntegral value))
narrowStoreT IntI64 width value = take width (bytesOfWord64 value)

-- | Move a typed host value in and out of the untyped 'Val' slot, so conversions can reuse
--   the shared 'convertVal'.
toVal :: SNumType t -> RuntimeHostType ('Num t) -> Val
toVal SI32 = fromI32
toVal SI64 = fromI64
toVal SF32 = fromF32
toVal SF64 = fromF64

fromVal :: SNumType t -> Val -> RuntimeHostType ('Num t)
fromVal SI32 = toI32
fromVal SI64 = toI64
fromVal SF32 = toF32
fromVal SF64 = toF64
