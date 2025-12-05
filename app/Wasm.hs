{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}


-- | A type-safe embedded domain-specific language (DSL) for WebAssembly.
-- This module uses advanced Haskell type system features to ensure that
-- WebAssembly programs are stack-safe and type-correct at compile time.
module Wasm where

import Data.Int (Int32)
import Data.Word (Word32, Word64)
import Types (WasmType(I64, I32), WasmType, ValStackShape, type (:+>+), CheckTopVecEqual, BlockType (..), FuncName, FuncTypeAnn (..), Take, FuncTypeAnn (..), Reverse, KnownWasmType (ForI32), LabelStackShape, GetLabelType, GetLabelCreationValStackLength, SomeValStackShape(..), KnownValStackShape (KnownValVNil, KnownValCons), GetSpecificValVec, LabelShape(..))
import Utils
import WasmModule (WasmModule(..), GetGlobals, GlobalTypeToWasmType, MemArg(SMemArg), WasmModuleShape(..), GetMemoriesShape, GetGlobalsShape, GlobalType(..), Mutability(..))

{-
=============================================================================
LOCAL VARIABLE CONTEXT
=============================================================================
-}

-- | Reference to a local variable slot (0-indexed).
type SlotIndex = Nat

type LocalsShape = [WasmType]

{- TODO: Better error messages
   Improve type error messages for common mistakes like:
   - Stack underflow
   - Type mismatches
   - Invalid local access
-}


{-
=============================================================================
INSTRUCTIONS
=============================================================================
-}

-- | WebAssembly instructions with static stack and local variable tracking.
-- Each instruction is parameterized by:
--   - inputStack: the stack shape before the instruction
--   - outputStack: the stack shape after the instruction
--   - locals: the local variable context (currently unchanged by most instructions)
data Instruction (inputStack :: ValStackShape) (outputStack :: ValStackShape) (locals :: LocalsShape) (wasmModule::WasmModule shape) (inputLabels:: LabelStackShape) (outputLabels :: LabelStackShape) where -- 

    -- Constants: push a literal value onto the stack
    I32Const :: Int32 -> Instruction inputStack ((I32 ': inputStack) :: ValStackShape) locals wasmModule inputLabels inputLabels

    -- i32 arithmetic operators (all pop two values, push one result)
    I32Add :: Instruction (I32 ': I32 ': inputStack) (I32 ': inputStack) locals wasmModule inputLabels inputLabels
    I32Sub :: Instruction (I32 ': I32 ': inputStack) (I32 ': inputStack) locals wasmModule inputLabels inputLabels
    I32Mul :: Instruction (I32 ': I32 ': inputStack) (I32 ': inputStack) locals wasmModule inputLabels inputLabels
    I32Div :: Instruction (I32 ': I32 ': inputStack) (I32 ': inputStack) locals wasmModule inputLabels inputLabels
    -- TODO: Handle division by zero at type level if WASM spec allows,
    --       otherwise document that this fails at runtime
    --       In spec it is defined as: if i2 is 0, then the result is undefined.
    --       Also I think division exists for signed and unsigned ints
    I32RemU :: Instruction (I32 ': I32 ': inputStack) (I32 ': inputStack) locals wasmModule inputLabels inputLabels  --remainder operation (unsigned)
    --      if i2 is zero then the output is undefined
    I32RemS :: Instruction (I32 ': I32 ': inputStack) (I32 ': inputStack) locals wasmModule inputLabels inputLabels  -- remainder operation (signed)
    --      if i2 is zero then the output is undefined -> the result has the sign of the first operator

    -- i32 comparison operators (pop two values, push i32 boolean result)
    I32EqZ :: Instruction (I32 ': inputStack) (I32 ': inputStack) locals wasmModule inputLabels inputLabels            -- test if zero
    I32Eq  :: Instruction (I32 ': I32 ': inputStack) (I32 ': inputStack) locals wasmModule inputLabels inputLabels    -- equal
    I32Neq :: Instruction (I32 ': I32 ': inputStack) (I32 ': inputStack) locals wasmModule inputLabels inputLabels    -- inequality
    I32LtS :: Instruction (I32 ': I32 ': inputStack) (I32 ': inputStack) locals wasmModule inputLabels inputLabels    -- less than (signed)
    I32LtU :: Instruction (I32 ': I32 ': inputStack) (I32 ': inputStack) locals wasmModule inputLabels inputLabels    -- less than (unsigned)
    I32LeS :: Instruction (I32 ': I32 ': inputStack) (I32 ': inputStack) locals wasmModule inputLabels inputLabels    -- less or equal (signed)
    I32LeU :: Instruction (I32 ': I32 ': inputStack) (I32 ': inputStack) locals wasmModule inputLabels inputLabels    -- less or equal (unsigned)
    I32GtS :: Instruction (I32 ': I32 ': inputStack) (I32 ': inputStack) locals wasmModule inputLabels inputLabels    -- greater than (signed)
    I32GtU :: Instruction (I32 ': I32 ': inputStack) (I32 ': inputStack) locals wasmModule inputLabels inputLabels    -- greater than (unsigned)
    I32GeS :: Instruction (I32 ': I32 ': inputStack) (I32 ': inputStack) locals wasmModule inputLabels inputLabels    -- greater or equal (signed)
    I32GeU :: Instruction (I32 ': I32 ': inputStack) (I32 ': inputStack) locals wasmModule inputLabels inputLabels    -- greater or equal (unsigned)
    -- more operators (e.g. bitwise negation, bitwise conjunction, ..., min, max)

    -- i64 arithmetic operators
    I64Add :: Instruction (I64 ': I64 ': inputStack) (I64 ': inputStack) locals wasmModule inputLabels inputLabels
    I64Sub :: Instruction (I64 ': I64 ': inputStack) (I64 ': inputStack) locals wasmModule inputLabels inputLabels
    I64Mul :: Instruction (I64 ': I64 ': inputStack) (I64 ': inputStack) locals wasmModule inputLabels inputLabels
    I64Div :: Instruction (I64 ': I64 ': inputStack) (I64 ': inputStack) locals wasmModule inputLabels inputLabels
    -- differentiation signed vs unsigned?
    I64RemU :: Instruction (I64 ': I64 ': inputStack) (I64 ': inputStack) locals wasmModule inputLabels inputLabels --remainder operation (unsigned)
    --      if i2 is zero then the output is undefined
    I64RemS :: Instruction (I64 ': I64 ': inputStack) (I64 ': inputStack) locals wasmModule inputLabels inputLabels -- remaidner operaton (signed)
    --      if i2 is zero then the output is undefined -> the result has the sign of the first operator

    -- I64 comparison operators
    I64EqZ :: Instruction (I64 ': inputStack) (I64 ': inputStack) locals wasmModule inputLabels inputLabels   -- test if equal to zero
    I64Eq  :: Instruction (I64 ': I64 ': inputStack) (I64 ': inputStack) locals wasmModule inputLabels inputLabels   -- equal
    I64Neq :: Instruction (I64 ': I64 ': inputStack) (I64 ': inputStack) locals wasmModule inputLabels inputLabels   -- inequality
    I64LeS :: Instruction (I64 ': I64 ': inputStack) (I64 ': inputStack) locals wasmModule inputLabels inputLabels   -- less or equal (signed)
    I64LeU :: Instruction (I64 ': I64 ': inputStack) (I64 ': inputStack) locals wasmModule inputLabels inputLabels   -- less or equal (unsigned)
    I64LtS :: Instruction (I64 ': I64 ': inputStack) (I64 ': inputStack) locals wasmModule inputLabels inputLabels   -- less than (signed)
    I64LtU :: Instruction (I64 ': I64 ': inputStack) (I64 ': inputStack) locals wasmModule inputLabels inputLabels   -- less than (unsigned)
    I64GtS :: Instruction (I64 ': I64 ': inputStack) (I64 ': inputStack) locals wasmModule inputLabels inputLabels   -- greater than (signed)
    I64GtU :: Instruction (I64 ': I64 ': inputStack) (I64 ': inputStack) locals wasmModule inputLabels inputLabels   -- greater than (unsigned)
    I64GeS :: Instruction (I64 ': I64 ': inputStack) (I64 ': inputStack) locals wasmModule inputLabels inputLabels   -- greater or equal (signed)
    I64GeU :: Instruction (I64 ': I64 ': inputStack) (I64 ': inputStack) locals wasmModule inputLabels inputLabels   -- greater or equal (unsigned)


    -- Stack manipulation
    Drop :: Instruction (dropped ': inputStack) inputStack locals wasmModule inputLabels inputLabels   -- remove top value from stack

    -- Local variable operations
    -- LocalGet: push the value of a local variable onto the stack
    LocalGet :: SFin i n
             -> Instruction inputStack (Index i locals ': inputStack) locals wasmModule inputLabels inputLabels

    -- LocalSet: pop a value from stack and store it in a local variable
    LocalSet :: SFin i n
             -> Instruction (Index i locals ': inputStack) inputStack locals wasmModule inputLabels inputLabels
    -- LocalTee:
    -- pop val from stack
    -- push val to stack
    -- push val to stack
    -- localSet
        -- pop val from stack
        -- local[i] = val
    -- => in the end value is still on top of the stack as well as saved in the locals
        -- => technically the stack looks the same at the start and at the end?
    LocalTee :: SFin i n
             -> Instruction (Index i locals ': inputStack) (Index i locals ': inputStack) locals wasmModule inputLabels inputLabels
    -- TODO: Handle uninitialized local variables according to WASM spec

    -- GlobalGet: push the value of a global variable onto the stack
    GlobalGet :: forall (i :: Nat) (n :: Nat) (m :: Nat) (l :: Nat) (ivs :: Nat) (shape :: WasmModuleShape) (inputStack :: ValStackShape) (wasmModule :: WasmModule shape) (locals :: LocalsShape) (inputLabels :: LabelStackShape).
        (n ~ GetGlobalsShape shape) =>
        SFin i n
        -> Instruction inputStack (GlobalTypeToWasmType (Index i (GetGlobals wasmModule)) ': inputStack) locals wasmModule inputLabels inputLabels

    -- GlobalSet: pop a value from stack and store it in a global variable => global type must be mutable where do we check this
    GlobalSet :: forall (i :: Nat) (n :: Nat) (m :: Nat) (l :: Nat) (ivs :: Nat) (shape :: WasmModuleShape) (inputStack :: ValStackShape) (wasmModule :: WasmModule shape) (locals :: LocalsShape) (inputLabels :: LabelStackShape).
        (n ~ GetGlobalsShape shape) =>
        SFin i n
        -> Instruction (GlobalTypeToWasmType (Index i (GetGlobals wasmModule)) ': inputStack) inputStack locals wasmModule inputLabels inputLabels


    -- MEMORY INSTRUCTIONS
    -- need to make this an annotated Function such that we can know whether we load an I32, I64, F32, F64
    -- do we even have to access the memory like this: (Index offset (GetMems wasmModule))
        -- this simply returns a memory type which includes the limits of the memory
    -- We need the forall in order to use MemoryLoad @I32
    -- type equality ~ or :~:
    MemoryLoad :: forall (wasmtype::WasmType) (i :: Nat) (n :: Nat) (m :: Nat) (k :: Nat) (ivs :: Nat) (shape :: WasmModuleShape) (align :: Word32) (offset :: Word64) (inputStack :: ValStackShape) (wasmModule :: WasmModule shape) (locals :: LocalsShape) (inputLabels :: LabelStackShape) .
        (n ~ GetMemoriesShape shape) => 
             SFin i n
             -> MemArg align offset  -- ignore alignment for now, also not 100% sure why i32 has to be on top of stack
             -> Instruction (I32 ': inputStack) (wasmtype ': inputStack) locals wasmModule inputLabels inputLabels
    -- MemoryStore: pop address and value from stack, store value at address in memory
        -- should we also make this annoted with the wasmtype?
    -- MemoryStore :: MemArg offset alignment -- add  constraint on limit of memory
    --          -> Instruction (I32 :> wasmtype :> inputStack) inputStack locals wasmModule

    -- MemoryStore with annotation to specify the type that is stored
    MemoryStore :: forall (wasmtype :: WasmType) (i :: Nat) (n :: Nat) (shape :: WasmModuleShape) align offset inputStack (wasmModule :: WasmModule shape) locals inputLabels outputLabels.
        (n ~ GetMemoriesShape shape) => 
        SFin i n
        -> MemArg align offset
        -> Instruction (I32 ': wasmtype ': inputStack) inputStack locals wasmModule inputLabels outputLabels


    -- Control flow instructions
    -- Block: a sequence of instructions that can be exited early with 'br'
    -- The stack shape arithmetic (+>+) ensures the block result sits on top of the input stack
    -- typeidx|[valtype?] => typeidx points to a type in the type section.
    -- valtype? represents a function type like [] -> [valtype?]
    -- so result of block can only be exactly one or no value
    -- also the result is the label type
    -- also the parameters of the block must be validated to be on top of the stack before entering!
    -- Block :: LabelIndex
    --       -> KnownStackShape outputShape -- represents the optional valtype however what about the typeidx? can't know the function type
    --       -> InstructionSequence inputStack (outputShape +>+ inputStack) locals wasmModule inputLabels outputLabels
    --       -> Instruction inputStack (outputShape +>+ inputStack) locals wasmModule inputLabels outputLabels
    
    
    -- technically the type like this would be defined at a type index in the types module
    -- Alternatively we can define just a WasmType in BlockType and then it would be the same as the func type []->[WasmType] => how should we go about it ? implement the types module? however not quite sure how we add types to the type module.
    Block :: forall (m :: Nat) (l :: Nat) (ps :: Nat) (rs :: Nat) (ivs :: Nat) (ovs :: Nat) (shape :: WasmModuleShape) (paramsStack :: ValStackShape) (resStack :: ValStackShape) (inputStack :: ValStackShape) (outputStack :: ValStackShape) (locals :: LocalsShape) (wasmModule :: WasmModule shape) (inputLabels :: LabelStackShape).
            (CheckTopVecEqual ('SomeValStackShape paramsStack) ('SomeValStackShape inputStack) ~ 'True,
                CheckTopVecEqual ('SomeValStackShape resStack) ('SomeValStackShape outputStack) ~ 'True)  -- ensure that the parameters of the block are on top of the input stack
          => BlockType paramsStack resStack -- represents the optional valtype however what about the typeidx? can't know the function type
          -> InstructionSequence inputStack outputStack locals wasmModule ('LabelShape resStack (GetVecLen inputStack) ': inputLabels) ('LabelShape resStack (GetVecLen inputStack) ': inputLabels)
          -> Instruction inputStack outputStack locals wasmModule inputLabels inputLabels

    -- Loop: a sequence of instructions that can be restarted with 'br'
    Loop  :: forall (m :: Nat) (l :: Nat) (ps :: Nat) (rs :: Nat) (ivs :: Nat) (ovs :: Nat) (shape :: WasmModuleShape) (paramsStack :: ValStackShape) (resStack :: ValStackShape) (inputStack :: ValStackShape) (outputStack :: ValStackShape) (locals :: LocalsShape m) (wasmModule :: WasmModule shape) (inputLabels :: LabelStackShape l).
            (CheckTopVecEqual ('SomeValStackShape paramsStack) ('SomeValStackShape inputStack) ~ 'True,
                CheckTopVecEqual ('SomeValStackShape resStack) ('SomeValStackShape outputStack) ~ 'True)  -- ensure that the parameters of the block are on top of the input stack
          => BlockType paramsStack resStack
          -> InstructionSequence inputStack outputStack locals wasmModule ('( 'SomeValStackShape paramsStack, GetVecLen inputStack) ': inputLabels) ('( 'SomeValStackShape paramsStack, GetVecLen inputStack) ': inputLabels)
          -> Instruction inputStack outputStack locals wasmModule inputLabels inputLabels

    -- If: conditional execution (pops i32 condition, executes one of two branches)
    If    :: (CheckTopVecEqual ('SomeValStackShape paramsStack) ('SomeValStackShape inputStack) ~ 'True,
                CheckTopVecEqual ('SomeValStackShape resStack) ('SomeValStackShape outputStack) ~ 'True)  -- ensure that the parameters of the block are on top of the input stack
          => BlockType paramsStack resStack
          -> InstructionSequence inputStack outputStack locals wasmModule ('( 'SomeValStackShape resStack, GetVecLen inputStack) ': inputLabels) ('( 'SomeValStackShape resStack, GetVecLen inputStack) ': inputLabels)     -- then branch
          -> InstructionSequence inputStack outputStack locals wasmModule ('( 'SomeValStackShape resStack, GetVecLen inputStack) ': inputLabels) ('( 'SomeValStackShape resStack, GetVecLen inputStack) ': inputLabels)     -- else branch
          -> Instruction (I32 ': inputStack) outputStack locals wasmModule inputLabels inputLabels

    -- Br: unconditional branch to a label
        -- Nat is the nesting depth of how many nested blocks/loops to break out of
        -- I guess this means we need an additional stack or vector that stores the current 
            -- block nesting depth
            -- this is needed because we want to be able to validate that the labelidx
                -- is not out of bounds.
        -- 2. need to validate that the input stack is some wasmtypes and the the labeltype
    
    -- Version that is close to what should be done in execution
    -- Br    ::  (LessThan n (StackLength labels) ~ 'True, -- check whether labelidx is valid
    --             PopTopUntilLabelFromStack n (StackLength (GetLabelType n labels)) Empty inputStack ~ GetLabelType n labels) =>
    --             -- second constraint checks:
    --             -- pops the top of the stack until the correctly nested label is found
    --             -- removes all the labels on the inputStack until there
    --             -- checks the arity of the label type
    --             -- returns the top of the stack with the correct arity
    --             -- compares whether now the top of the stack is equal to the label type
    --           StackIndex n
    --           -> Instruction inputStack outputStack locals wasmModule labels

    -- This does not compile
    -- Br   :: forall (i::Nat) (l :: Nat) (n ::Nat) (m::Nat) (inputLabels :: LabelStack ('S l)) (inputStack :: StackShape) (outputStack :: StackShape) (locals :: LocalsShape n) (wasmModule :: WasmModule m).
    --         StackIndex i l
    --         -> Instruction (GetLabelType i inputLabels +>+ inputStack) outputStack locals wasmModule inputLabels (RemoveLabels i inputLabels) -- after branching, the labels above the target label are removed from the label stack?

    -- This version compiles
    -- Checks whether the top of the input stack is equal to the label type as a constraint
    Br    :: forall (labelLength :: Nat) (creationLength :: Nat) (i :: Nat) (l :: Nat) (n :: Nat) (ivs :: Nat) (ovs :: Nat) (shape :: WasmModuleShape) (inputLabels :: LabelStackShape l) (inputStack :: ValStackShape ivs) (outputStack :: ValStackShape (labelLength :+ creationLength)) (labelType :: SomeValStackShape) (locals :: LocalsShape n) (wasmModule :: WasmModule shape) .
        (CheckTopVecEqual (GetLabelType (Index i inputLabels)) ( 'SomeValStackShape inputStack) ~ 'True,
        labelLength ~ GetVecLen (GetSpecificValVec(GetLabelType (Index i inputLabels))),
        -- labelLength ~ GetVecLen (GetSpecificValVec(GetLabelType (Index i inputLabels))),
        creationLength ~ GetLabelCreationValStackLength (Index i inputLabels),
        -- creationLength ~ GetLabelCreationValStackLength (Index i inputLabels),
        -- '(labelType, creationLength) ~ Index i inputLabels,
        -- labelLength ~ GetVecLen (GetSpecificValVec labelType),
        ovs ~ labelLength :+ creationLength,
        (Take labelLength inputStack :+>+
          Take creationLength (Reverse inputStack))
          ~ outputStack,
          l ~ GetVecLen inputLabels
        ) => 
            SFin i l
            -> Instruction inputStack
                           outputStack
                           locals
                           wasmModule
                           inputLabels
                           inputLabels

    -- BrIf: conditional branch (pops i32 condition)
    -- DINA: Problem => either we branch then we have the conditions below for the outputStack or we don't branch
    -- and then the outputStack is just the inputStack minus the i32 condition
    BrIf  :: forall (i :: Nat) (l :: Nat) (n :: Nat) (ivs :: Nat) (shape :: WasmModuleShape) (inputLabels :: LabelStackShape l) (inputStack :: ValStackShape ivs) (locals :: LocalsShape n) (wasmModule :: WasmModule shape) .
    -- inputStack ~ outputStack =>
        (CheckTopVecEqual (GetLabelType (Index i inputLabels)) ( 'SomeValStackShape inputStack) ~ 'True) =>
        SFin i l 
        -> Instruction (I32 ': inputStack) inputStack locals wasmModule inputLabels inputLabels

    -- "naive" way
    Call  :: FuncName -> FuncTypeAnn inputStack outputStack -> Instruction inputStack outputStack locals wasmModule inputLabels outputLabels 

    -- here we need to po
    -- Call  :: FuncName f -> Instruction (GetParamsOf (GetTypeOfFunc f wasmModule)) (GetResultsOf (GetTypeOfFunc f wasmModule)) locals wasmModule inputLabels outputLabels 

    -- TODO: missing WASM instructions

    Leave :: SNat n -> Instruction inputStack inputStack locals wasmModule inputLabels inputLabels

{-
=============================================================================
INSTRUCTION SEQUENCES
=============================================================================
-}

-- | A sequence of WebAssembly instructions.
-- This represents a linear sequence of instructions where the output stack
-- of one instruction becomes the input stack of the next.
infixr 5 :|  -- Right-associative, like list construction
data InstructionSequence (inputStack :: ValStackShape) (outputStack :: ValStackShape) (locals :: LocalsShape) (wasmModule :: WasmModule shape) (inputLabels :: LabelStackShape) (outputLabels :: LabelStackShape) where
    End  :: InstructionSequence inputStack inputStack locals wasmModule inputLabels inputLabels   -- Base case: empty sequence (identity)
    (:|) :: Instruction initialStack intermediateStack locals wasmModule inputLabels intermediateLabels               -- Inductive case: first instruction
         -> InstructionSequence intermediateStack finalStack locals wasmModule intermediateLabels outputLabels                          -- rest of sequence
         -> InstructionSequence initialStack finalStack locals wasmModule inputLabels outputLabels                              -- combined sequence

{-
=============================================================================
FUNCTIONS
=============================================================================
-}

-- | A complete WebAssembly function.
-- Functions start with an empty stack and produce the specified final stack shape.
-- The locals context represents the function's parameters and local variables.
data Function (inputStack :: ValStackShape ivs) (resultStack :: ValStackShape ovs) (locals :: LocalsShape n) (outputLabels :: LabelStackShape l) (wasmModule :: WasmModule shape) where
    Function :: FuncTypeAnn inputStack resultStack -> InstructionSequence inputStack resultStack locals wasmModule outputLabels outputLabels -> Function inputStack resultStack locals outputLabels wasmModule
    -- add a new type that captures the function type annotation, i.e.
    -- FuncTypeAnn inputStack resultStack ->






{-
=============================================================================
EXAMPLE FUNCTIONS
=============================================================================
-}

-- Example Call in Function
callExample :: forall (s :: WasmModuleShape) (wm :: WasmModule s) . (s ~ WasmModuleShapeR Z Z) => Function VNil (I32 ': VNil) (I32 ': I32 ': VNil) VNil wm
callExample = Function (FFuncTypeAnn [] (I32 : [])) $
       LocalGet SFZ    -- get first parameter
    :| LocalGet (SFS SFZ)  -- get second parameter
    :| Call "add2" (FFuncTypeAnn (I32 : (I32 : [])) (I32 : [])) -- call add2 function
    :| End

-- Example MemoryLoad
-- the locals are the two I32 integers that are used to compute the address of the memory load
-- memLoadSequence :: Function EmptyValStack (I64 :> EmptyValStack) (I32 ': I32 ': VNil) EmptyLabels ((WasmModuleR VNil ('[ 'SomeWasmType ( RInt32 (fromIntegral 10 :: Int32)), 'SomeWasmType ( RInt32 (fromIntegral 20 :: Int32))] ': VNil)) :: WasmModule ( WasmModuleShapeR Z (S Z)))

memLoadSequence :: Function VNil (I64 ': VNil) (I32 ': I32 ': VNil) VNil ((WasmModuleR VNil ('[ fromIntegral 10::Int32, fromIntegral 20::Int32 ] ': VNil)) :: WasmModule ( WasmModuleShapeR Z (S Z)))
memLoadSequence = Function (FFuncTypeAnn [] (I64 : [])) $
       LocalGet SFZ
    :| MemoryLoad @I64 SFZ (SMemArg 0 0) 
    :| LocalGet (SFS SFZ)
    :| MemoryLoad @I64 SFZ (SMemArg 0 0)
    :| I64Add 
    :| End

-- Example MemoryStore
-- memstoresequence :: Function EmptyValStack EmptyValStack (I32 ': I64 ': VNil) EmptyLabels ((WasmModuleR VNil (MemoryTypeR (LimitsR (fromIntegral 0 Word64) Nothing) '[] ': VNil)) :: WasmModule ( WasmModuleShapeR Z (S Z)))
memstoresequence :: Function VNil VNil (I32 ': I64 ': VNil) VNil ((WasmModuleR VNil ('[] ': VNil)) :: WasmModule ( WasmModuleShapeR Z (S Z)))
memstoresequence = Function (FFuncTypeAnn VNil VNil) $
       LocalGet (SFS SFZ)  -- get the address
    :| LocalGet SFZ      -- get the value to store
    :| MemoryStore @I64 SFZ (SMemArg 0 0)
    :| End

-- Example GlobalGet and GlobalSet
-- have to force the WasmModuleShape so :: WasmModule (WasmModuleShapeR (S Z) Z) is necessary!!!
globalGetSetSequence :: Function VNil (I32 ': VNil) VNil VNil ((WasmModuleR (GlobalTypeMW Var I32 ': VNil) VNil) :: WasmModule ( WasmModuleShapeR (S Z) Z))
globalGetSetSequence = Function (FFuncTypeAnn VNil (I32 : VNil)) $
       GlobalGet SFZ        -- get global at index 0
    :| I32Const 10
    :| I32Add
    :| GlobalSet SFZ      -- set global at index 0
    :| GlobalGet SFZ      -- get global at index 0 again
    :| End

-- add1Sequence :: InstructionSequence (I32 :> I32 :> Empty) (I32 :> Empty) 'VNil ('WasmModule '[]) ('WasmModule '[])
add1Sequence :: forall {n :: Nat} {k :: Nat} {ivs :: Nat} {shape :: WasmModuleShape} {inputStack :: ValStackShape ivs} {locals :: LocalsShape n} {wasmModule :: WasmModule shape} {inputLabels :: LabelStackShape k}. InstructionSequence (I32 ': (I32 ': inputStack)) (I32 ': inputStack) locals wasmModule inputLabels inputLabels
add1Sequence = I32Add :| End

-- addSubSequence :: InstructionSequence (I32 :> (I32 :> (I32 :> Empty))) (I32 :> Empty) 'VNil (WasmModule Z) ('WasmModule '[]) -- only 3 I32 because the result of the add is the first argument of the subtract
addSubSequence :: forall {n :: Nat} {k :: Nat} {ivs :: Nat} {shape :: WasmModuleShape} {inputStack :: ValStackShape ivs} {locals :: LocalsShape n} {wasmModule :: WasmModule shape} {inputLabels :: LabelStackShape k}. InstructionSequence (I32 ': (I32 ': (I32 ': inputStack))) (I32 ': inputStack) locals wasmModule inputLabels inputLabels
addSubSequence = I32Add :| (I32Sub :| End)

-- example function for Br instruction
-- branchExample :: forall (s :: WasmModuleShape) (wm :: WasmModule s) . (s ~ WasmModuleShapeR Z Z) => Function VNil VNil (I32 ': VNil) ('(VNil, Z) ': EmptyLabels) wm
branchExample :: Function VNil VNil (I32 ': VNil) ('( 'SomeValStackShape VNil, Z) ': VNil) ((WasmModuleR VNil VNil) :: WasmModule ( WasmModuleShapeR Z Z))
branchExample = Function (FFuncTypeAnn VNil VNil) $
       Block (BTParamsResults KnownValVNil KnownValVNil) (
        Br (SFS SFZ)
        :| End)
    :| End

    -- example function for Br instruction
branchExample2 ::forall (s :: WasmModuleShape) (wm :: WasmModule s) . (s ~ WasmModuleShapeR Z Z) =>  Function VNil VNil (I32 ': VNil) ('( 'SomeValStackShape VNil, Z) ': VNil) wm
branchExample2 = Function (FFuncTypeAnn VNil VNil) $
       Block (BTParamsResults KnownValVNil KnownValVNil) (
        Br SFZ
        :| End)
    :| Br SFZ
    :| End

    -- example function for Br instruction
branchExample3 :: forall (s :: WasmModuleShape) (wm :: WasmModule s) . (s ~ WasmModuleShapeR Z Z) =>  Function VNil (I32 ': VNil) (I32 ': VNil) VNil wm
branchExample3 = Function (FFuncTypeAnn VNil VNil) $
       Block (BTParamsResults KnownValVNil (KnownValCons ForI32 KnownValVNil)) (
        Block (BTParamsResults KnownValVNil KnownValVNil) (
            Br SFZ
            :| End)
        :| I32Const 42
        :| Br SFZ
        :| End
        )
    :| End

-- example function for Br instruction
branchExample4 :: forall (s :: WasmModuleShape) (wm :: WasmModule s) . (s ~ WasmModuleShapeR Z Z) => Function VNil (I32 ': VNil) (I32 ': VNil) VNil wm
branchExample4 = Function (FFuncTypeAnn VNil VNil) $
       Block (BTParamsResults KnownValVNil (KnownValCons ForI32 KnownValVNil)) (
        Block (BTParamsResults KnownValVNil KnownValVNil) (
            I32Const 42
            :| Br (SFS SFZ)
            :| End)
        -- :| Br StackIndexZ
        :| End
        )
    :| End

-- | Example 1: Add two integers
-- Takes two i32 parameters (slots 0 and 1), returns their sum
add2 :: forall (s :: WasmModuleShape) (wm :: WasmModule s) . (s ~ WasmModuleShapeR Z Z) => Function VNil (I32 ': VNil) (I32 ': I32 ': VNil) VNil wm -- Function resultStack locals (repr the function parameters)
add2 = Function (FFuncTypeAnn VNil (I32 : VNil)) $
    -- Local slots: (0) first parameter, (1) second parameter
       LocalGet SFZ    -- Push first parameter
    :| LocalGet (SFS SFZ)     -- Push second parameter
    :| I32Add               -- Add them (pops 2, pushes 1 result)
    :| End

-- | Example 2: Factorial function using iteration
-- Takes one i32 parameter, returns its factorial
factorial :: forall (s :: WasmModuleShape) (wm :: WasmModule s) . (s ~ WasmModuleShapeR Z Z) => Function VNil (I32 ': VNil) (I32 ': I32 ': VNil) VNil wm
factorial = Function (FFuncTypeAnn VNil (I32 : VNil)) $
    -- Local slots: (0) input parameter (also used as counter), (1) accumulator
    -- Initialize accumulator to 1
       I32Const 1
    :| LocalSet (SFS SFZ)
    -- :| I32Const 0
    -- Main computation block
    :| Block (BTParamsResults KnownValVNil KnownValVNil) (
        -- Check if n <= 1 (base case)
           LocalGet SFZ
        :| I32Const 1
        :| I32LeS
        :| BrIf SFZ             -- Exit block if n <= 1
        -- Iterative loop for factorial computation
        :| Loop (BTParamsResults KnownValVNil KnownValVNil) (
            -- accumulator *= n
               LocalGet (SFS SFZ)
            :| LocalGet SFZ
            :| I32Mul
            :| LocalSet (SFS SFZ)
            -- n -= 1
            :| LocalGet SFZ
            :| I32Const 1
            :| I32Sub
            :| LocalSet SFZ
            -- Continue if n > 1
            :| LocalGet SFZ
            :| I32Const 1
            :| I32GtS
            :| BrIf (SFS SFZ)             -- Branch back to loop start
            :| End)
        :| End)
    -- Return the accumulated result
    :| LocalGet (SFS SFZ)
    :| End

-- | Example 3: Function that returns nothing (void function).
-- Demonstrates different return types - this one returns Empty stack.
printNumber :: forall (s :: WasmModuleShape) (wm :: WasmModule s) . (s ~ WasmModuleShapeR Z Z) => Function VNil VNil (I32 ': VNil) VNil wm
printNumber = Function (FFuncTypeAnn VNil VNil) $
    -- Just consume the parameter without returning anything
       LocalGet slotZero
    :| Drop
    :| End
    where
      -- example: here we are saying that
      -- extract the zeroth index from
      -- a vector of size 2
      slotZero :: SFin 'Z ('S ('S 'Z))
      slotZero = SFZ

-- | Example 4: Function with more complex local variable patterns.
-- Takes one parameter, uses three local variables for intermediate calculations.
complexCalculation :: forall (s :: WasmModuleShape) (wm :: WasmModule s) . (s ~ WasmModuleShapeR Z Z) => Function VNil (I32 ': VNil) (I32 ': I32 ': I32 ': I32 ': VNil) VNil wm
complexCalculation = Function (FFuncTypeAnn VNil (I32 : VNil)) $
    -- Local slots: (0) input, (1) temp1, (2) temp2, (3) result
    -- temp1 = input * 2
       LocalGet SFZ
    :| I32Const 2
    :| I32Mul
    :| LocalSet (SFS SFZ)
    -- temp2 = input + 10
    :| LocalGet SFZ
    :| I32Const 10
    :| I32Add
    -- TODO: Need more slot witnesses for slots 2 and 3
    -- This is incomplete but shows the pattern
    :| End

-- | Example 5: Conditional logic with If instruction.
-- Returns the absolute value of the input.
absoluteValue :: forall (s :: WasmModuleShape) (wm :: WasmModule s) . (s ~ WasmModuleShapeR Z Z) => Function VNil (I32 ': VNil) (I32 ': VNil) VNil wm
absoluteValue = Function (FFuncTypeAnn VNil (I32 : VNil)) $
    -- Check if input is negative
       LocalGet SFZ
    :| I32Const 0
    :| I32LtS              -- Is input < 0?
    :| If (BTParamsResults KnownValVNil KnownValVNil)
        -- Then branch: negate the number (0 - input)
        (  I32Const 0
        :| LocalGet SFZ
        :| I32Sub
        :| End)
        -- Else branch: return input as-is
        (  LocalGet SFZ
        :| End)
    :| End

-- Bad example (fails at compile time)
--nestedControlFlow :: Function (I32 :> Empty) (I32 ': I32 ': '[])
--nestedControlFlow = Function $
--    -- Outer block
--       Block 0 (ReturnsOne ForI32) (
--           LocalGet SFZ
--        :| I32Const 10
--        :| I32GtS
--        :| BrIf 0  -- Exit outer block if input > 10
--        -- Inner block
--        :| Block 1 NoReturn (
--               LocalGet SFZ
--            :| I32Const 5
--            :| I32LtS
--            :| BrIf 1  -- Exit inner block if input < 5
--            -- If we're here, 5 <= input <= 10
--            :| LocalGet SFZ
--            :| I32Const 2
--            :| I32Mul
--            :| LocalSet (SFS SFZ)
--            :| End)
--        -- Default case: return input unchanged
--        :| LocalGet SFZ
--        :| End)
--    :| LocalGet (SFS SFZ)  -- Return the result
--    :| End
