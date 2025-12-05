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
module WasmInterpreter where

import Data.Int (Int32, Int64)
import Data.Word (Word32, Word64)
import Types -- (RuntimeTypeOf(..), ValStackShape(..), BlockType (..),  FuncTypeAnn (..), knownStackShapeLen, Take, Drop, FuncTypeAnn (..), Reverse, WasmType (I32), KnownWasmType (ForI32, ForI64), RuntimeWasmTypes(..), (:+>+), type (+>+:), KnownValStackShape(..), LabelStackShape, SomeValStackShape(..), GetSpecificValVec, GetLabelType, GetLabelCreationValStackLength)
import Utils
import WasmModule (WasmModule(..), GetGlobals, GlobalTypeToWasmType, GlobalsShape, GlobalType (GlobalTypeMW), KnownMutability(SVar, SConst), GetMems, GetMemoriesShape, MemoriesShape, Limits(..), MemArg (SMemArg), MemoryArray) --, SomeWasmType (SomeWasmType))
import Wasm
import GHC.Base (RuntimeRep)
{-
=============================================================================
INTERPRETER
=============================================================================
-}

-- | Runtime representation of the WebAssembly stack.
-- This is the actual data structure that holds stack values during execution.
data Stack (stackShape :: ValStackShape) where
    EmptyStack :: Stack '[]
    Push       :: forall wasmType stackShape . RuntimeTypeOf wasmType -> Stack stackShape -> Stack (wasmType : stackShape)

-- stackLength :: Stack (stackShape :: ValStackShape s) -> SNat s
-- stackLength EmptyStack       = SZ
-- stackLength (Push _ rest) = SS (stackLength rest)

stackLength :: Stack (stackShape :: ValStackShape) -> SNat (Length stackShape)
stackLength EmptyStack       = SZ
stackLength (Push _ rest) = SS (stackLength rest)


takeStack :: () => SNat n -> Stack s -> (Stack (Take n s), Stack (Drop n s))
takeStack SZ stk = (EmptyStack, stk)
takeStack (SS n) (Push x xs) =
  let (taken, rest) = takeStack n xs
  in (Push x taken, rest)
takeStack (SS _) EmptyStack = error "takeStack: stack underflow"


concatStacks :: Stack s1 -> Stack s2 -> Stack (s1 :+>+ s2)
concatStacks s2 EmptyStack      = s2
concatStacks s2 (Push val rest) = Push val (concatStacks s2 rest)



-- type family GetArity (label :: Label a h) :: Nat where
--     GetArity '(arity :: SNat a, _) = a
-- type family GetArity (label :: Label) :: Nat where
--     GetArity '(arity, _) = arity

-- type family GetHeight (label :: Label shape) :: Nat where
--     GetHeight '(_, height :: SNat h) = h
-- type family GetHeight (label :: Label) :: Nat where
--     GetHeight '(_, height) = height

-- data RuntimeLabels (labels :: Labels l) where
--     RuntimeNoLabels :: RuntimeLabels 'NoLabels
--     RuntimeConsLabels :: Label a h -> RuntimeLabels labels -> RuntimeLabels (ConsLabels '(arity, height) labels)
-- data SomeLabels where
--     SomeLabels :: Labels labelsShape -> SomeLabels

-- data SomeLabel where
--     SomeLabel :: Label a h -> SomeLabel

data Label (shape :: LabelShape) = Label {
    arity :: SNat (Arity shape),
    height :: SNat (Height shape)
    -- continuation :: ...
}

-- popNthLabelFromTop ::
--     -- (label ~ LabelIndex n (labels :: Labels (labelStackShape :: LabelStackShape l))) =>
--     SFin n l
--     -> Labels (labelStackShape :: LabelStackShape l)
--     -> Label (Length (GetSpecificValVec (GetLabelType label))) (GetLabelCreationValStackLength label)
-- popNthLabelFromTop SFZ (ConsLabels label rest) = label
-- popNthLabelFromTop (SFS idx) (ConsLabels _ rest) = popNthLabelFromTop idx rest
    -- (a ~ Length (GetSpecificValVec (GetLabelType (Index n labelStackShape)))) =>
    -- ((label :: Label a h) ~ (LabelIndex n (labels :: Labels labelStackShape))) =>
     -- (labels :: Labels (labelStackShape :: LabelStackShape l))
    -- -> Label (Length (GetSpecificValVec (GetLabelType (Index n labelStackShape)))) (GetLabelCreationValStackLength (Index n labelStackShape))
    -- -> Label (GetArity (LabelIndex n (labels :: Labels labelStackShape))) (GetHeight (LabelIndex n (labels :: Labels labelStackShape)))
-- popNthLabelFromTop SFZ ((SomeLabels (ConsLabels label rest)) :: SomeLabels) = label :: Label (GetArity (LabelIndex 'Z (labels))) (GetHeight (LabelIndex 'Z (labels)))
-- popNthLabelFromTop SFZ ((SomeLabels (ConsLabels label rest)) :: SomeLabels) = SomeLabel label
-- popNthLabelFromTop (SFS idx) (SomeLabels (ConsLabels _ rest)) = popNthLabelFromTop idx (SomeLabels rest)
getAtLabel :: (l ~ Length labelStackShape) =>
    SFin n l
    -> Labels (labelStackShape :: LabelStackShape)
    -> Label (Index n labelStackShape)
getAtLabel SFZ (ConsLabels label _) = label
getAtLabel (SFS idx) (ConsLabels _ rest) = getAtLabel idx rest




-- Should pop the nth label from the top of the label stack
-- popNthLabelFromTop :: 
--             forall (a :: Nat) (h :: Nat) (n :: Nat) (l :: Nat) (allLabels :: Labels l) .(a ~ GetArity (GetRunTimeLabelEntry (l :- S n) allLabels),
--             h ~ GetHeight (GetRunTimeLabelEntry (l :- 'S n) allLabels)) => 
--             SFin n l
--             -> Labels l
--             -- -> (SNat (GetArity (GetRunTimeLabelEntry (l :- 'S n) allLabels)), SNat (GetHeight (GetRunTimeLabelEntry (l :- 'S n) allLabels)))
--             -> (Nat, Nat)
-- popNthLabelFromTop (SFZ :: SFin n l) (ConsLabels ( labelTypeArity, lenInputStack) _) =  (labelTypeArity, lenInputStack) --(labelTypeArity :: SNat (GetArity (GetRunTimeLabelEntry (l :- 'S n) allLabels)), lenInputStack :: SNat (GetHeight (GetRunTimeLabelEntry (l :- 'S n) allLabels))) -- :: (SNat (LenStackShape(GetLabelType (S n) restLabelsShape)))
-- popNthLabelFromTop (SFS idx) (ConsLabels (_, _) rest) = popNthLabelFromTop idx rest

-- popNthLabelFromTop :: 
--             SFin n ('S l)
--             -> Labels (('(arity, height) :>: (restLabelsShape :: LabelStackShape l)) :: LabelStackShape ('S l))
--             -> (SNat (LenStackShape arity), SNat height)
-- popNthLabelFromTop SFZ ((ConsLabels labelTypeArity lenInputStack _) :: Labels (restLabelsShape :: LabelStackShape l)) = (labelTypeArity, lenInputStack) -- :: (SNat (LenStackShape(GetLabelType (S n) restLabelsShape)))
-- popNthLabelFromTop (SFS (idx :: SFin n1 l1)) ((ConsLabels _ _ rest) :: Labels (top :>: remainingLabels)) = popNthLabelFromTop idx rest


reduceStackToLength :: forall n stackShape.
                       SNat n
                    -> Stack stackShape
                    -> Stack (Take n (Reverse stackShape))
reduceStackToLength n = fst . takeStack n . reverseStack

reverseStack :: Stack stackShape -> Stack (Reverse stackShape)
reverseStack EmptyStack = EmptyStack
reverseStack (Push @wasmType val rest) =
  concatStacks (reverseStack rest) (Push @wasmType val EmptyStack)




-- | Runtime representation of the WebAssembly locals.
-- This is the actual data structure that holds local values during execution.
data Locals (localsShape :: LocalsShape) where
    NoLocals   :: Locals '[]
    ConsLocals :: RuntimeTypeOf wasmType -> Locals localsShape -> Locals (wasmType : localsShape)

data Globals (globalsShape :: GlobalsShape) where
    NoGlobals   :: Globals '[]
    ConsGlobals :: RuntimeTypeOf wasmType -> KnownMutability m -> Globals globalsShape -> Globals (GlobalTypeMW m wasmType : globalsShape)

-- inside a label on the stack we savw
    -- the label stack Shape (so the types on the top of the value stack when the label is accessed)
    -- the length of the value stack when the label was created
    -- the continuation of the label (what should be executed when e.g. br is called)
data Labels (newLabelsShape :: LabelStackShape) where
    NoLabels :: Labels '[]
    ConsLabels :: 
    -- SNat (LenStackShape a) -> SNat h -> Labels (labelsShape :: LabelStackShape n) -> Labels ('(a :: ValStackShape, h:: Nat) :>: labelsShape) -- (newLabelsShape :: LabelStackShape ('S n))
       Label shape 
       -> Labels labelStackShape
       -> Labels ( shape : labelStackShape) -- (newLabelsShape :: LabelStackShape ('S n))
    
-- type family LabelIndex (i :: Nat) (labels :: Labels n) :: Label a h where
--     LabelIndex 'Z ((ConsLabels (label :: Label (Length (GetSpecificValVec ( 'SomeValStackShape v))) h) _) :: Labels ('( 'SomeValStackShape v, h) :<| labelStackShape)) = (label :: Label (Length (GetSpecificValVec (GetLabelType (Index 'Z ('( 'SomeValStackShape v, h) :<| labelStackShape))))) (GetLabelCreationValStackLength (Index 'Z ('( 'SomeValStackShape v, h) :<| labelStackShape))))
--     LabelIndex ('S n) (ConsLabels _ rest) = LabelIndex n rest

-- type family LabelIndex (i :: Nat) (labels :: Labels n) :: Label where
--     LabelIndex 'Z (ConsLabels label _)      = label
--     LabelIndex ('S n) (ConsLabels _ rest) = LabelIndex n rest

data Memory (memsShape :: MemoriesShape) where
    NoMems   :: Memory '[]
    ConsMems :: MemoryArray -> Memory memsShape -> Memory (memArray : memsShape)


data RuntimeContext (stackShape :: ValStackShape) (localsShape :: LocalsShape) (wasmModule :: WasmModule shape) (labelsShape :: LabelStackShape) = RuntimeContext
    { stack  :: Stack stackShape,
      locals :: Locals localsShape,
      globals :: Globals (GetGlobals wasmModule), -- :: GlobalsShape (GetGlobalsShape shape)),
      labels :: Labels labelsShape,
      memories :: Memory (GetMems wasmModule)
      -- TODO: labels, tables, etc.
    }

-- function to get the value of a local variable at a given index
getLocalValue :: SFin i n -> Locals localsShape -> RuntimeTypeOf (Index i localsShape)
getLocalValue SFZ (ConsLocals val _) = val
getLocalValue (SFS idx) (ConsLocals _ rest) = getLocalValue idx rest
getLocalValue _ NoLocals = error "Index out of bounds in getLocalValue"

-- function to set the value of a local variable at a given index
setLocalValue :: SFin i n -> RuntimeTypeOf (Index i localsShape) -> Locals localsShape -> Locals localsShape
setLocalValue SFZ newVal (ConsLocals _ rest) = ConsLocals newVal rest
setLocalValue (SFS idx) newVal (ConsLocals val rest) = ConsLocals val (setLocalValue idx newVal rest)
setLocalValue _ _ NoLocals = error "Index out of bounds in setLocalValue"

-- function to get the value of a global variable at a given index
getGlobalValue :: SFin i n -> Globals globalsShape -> RuntimeTypeOf (GlobalTypeToWasmType (Index i globalsShape))
getGlobalValue SFZ (ConsGlobals val _ _) = val
getGlobalValue (SFS idx) (ConsGlobals _ _ rest) = getGlobalValue idx rest
getGlobalValue _ NoGlobals = error "Index out of bounds in getGlobalValue"

--function to set the value of a global variable at a given index, mutability has to be var
setGlobalValue :: SFin i n -> RuntimeTypeOf (GlobalTypeToWasmType (Index i globalsShape)) -> Globals globalsShape -> Globals globalsShape
setGlobalValue SFZ newVal (ConsGlobals _ SVar rest) = ConsGlobals newVal SVar rest
setGlobalValue (SFS idx) newVal (ConsGlobals oldVal SVar rest) = ConsGlobals oldVal SVar (setGlobalValue idx newVal rest)
setGlobalValue _ _ (ConsGlobals _ SConst _) = error "Cannot set value of a constant global variable" -- TODO: double check this
setGlobalValue _ _ NoGlobals = error "Index out of bounds in setGlobalValue"


-- getMemArrayFromMemType :: RuntimeTypeOfMemory memType -> GetMemArrayFromMemoryType memType
-- getMemArrayFromMemType (RuntimeTypeOfMemory (MemoryTypeR _ types)) = RTOLWT types

-- function to get the array of a memory at a given index
getMemoryArray :: SFin i n -> Memory memsShape -> MemoryArray
getMemoryArray SFZ (ConsMems memArray _) = memArray
getMemoryArray (SFS idx) (ConsMems _ rest) = getMemoryArray idx rest
getMemoryArray _ NoMems = error "Index out of bounds in getMemoryArray"


-- getRuntimeTypeOf :: RuntimeWasmTypes t -> RuntimeTypeOf t
-- getRuntimeTypeOf (RInt32 x) = x
-- getRuntimeTypeOf (RInt64 x) = x
-- function to get the memory at a specified index
-- getMemory :: SFin i n -> Memory memsShape -> RuntimeTypeOfListWasmType (GetMemArrayFromMemoryType (Index i memsShape))
-- getMemory SFZ (ConsMems (RuntimeTypeOfMemory val) _) = val


data RuntimeInstr (instr :: Instruction inputStack outputStack locals wasmModule inputLabels outputLabels) where
    RInstr :: Instruction inputStack outputStack locals wasmModule inputLabels outputLabels
           -> RuntimeInstr instr

data RuntimeInstrSeq (instrSeq :: InstructionSequence inputStack outputStack locals wasmModule inputLabels outputLabels) where
    REnd  :: RuntimeInstrSeq 'End
    RCons :: RuntimeInstr (instr :: Instruction inputStack intermediateStack locals wasmModule inputLabels intermediateLabels)
          -> RuntimeInstrSeq restInstrSeq
          -> RuntimeInstrSeq (instr :| restInstrSeq)


-- executeBody :: forall inputStack outputStack locals wasmModule inputLabels outputLabels intermediateStack intermediateLabels .
--             -- ((firstInstr :: Instruction inputStack intermediateStack locals wasmModule inputLabels intermediateLabels) :| restInstr ~ totalInstr) => 
--             -- InstructionSequence inputStack outputStack locals wasmModule inputLabels outputLabels
--             -- RuntimeInstrSeq (totalInstr :: InstructionSequence inputStack outputStack locals wasmModule inputLabels outputLabels)
--             -- RuntimeInstrSeq ((firstInstr :: Instruction inputStack intermediateStack locals wasmModule inputLabels intermediateLabels) :| (restInstr :: InstructionSequence intermediateStack outputStack locals wasmModule intermediateLabels outputLabels))
--             Instruction inputStack intermediateStack locals wasmModule inputLabels intermediateLabels
--             -> InstructionSequence intermediateStack outputStack locals wasmModule intermediateLabels outputLabels
--             -> RuntimeContext inputStack locals wasmModule inputLabels
--             -> (InstructionSequence outputStack outputStack locals wasmModule outputLabels outputLabels, 
--                  RuntimeContext outputStack locals wasmModule outputLabels)
-- executeBody instr instrSeq prevCtxt = case instrSeq of
--     End -> (End, executeInstruction instr prevCtxt)
--         -- let intermediateCtxt = executeInstruction instr prevCtxt
--         -- in (REnd :: RuntimeInstrSeq restInstr,
--         --           intermediateCtxt :: RuntimeContext outputStack locals wasmModule outputLabels)
--     (Leave SZ) :| rest -> let (topLabel, restLabels) = popNthLabel SFZ (labels prevCtxt)
--         in undefined
--     (Leave index) :| rest -> undefined
--     (i :| rest) -> 
--         let intermediateCtxt = executeInstruction instr prevCtxt
--             (finalInstrSeq, finalCtxt) = executeBody i rest intermediateCtxt
--         in (finalInstrSeq, finalCtxt)


-- TODO
executeInstruction :: forall inputStack outputStack locals wasmModule inputLabels outputLabels .
                      Instruction inputStack outputStack locals wasmModule inputLabels outputLabels
                   -> RuntimeContext inputStack locals wasmModule inputLabels
                   -> RuntimeContext outputStack locals wasmModule outputLabels
                --    -> RuntimeContext inputStack locals wasmModule (LenLabelStackShape inputLabels)
                --    -> RuntimeContext outputStack locals wasmModule (LenLabelStackShape outputLabels)
executeInstruction instr prevCtxt@(RuntimeContext prevStack prevLocals prevGlobal prevLabels prevMemory) = case instr of
    I32Const val -> RuntimeContext (Push val prevStack) prevLocals prevGlobal prevLabels prevMemory
    I32Add       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 + val1
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels prevMemory
    I32Sub       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val1 - val2 -- TODO double check the order!!
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels prevMemory
    I32Mul       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 * val1
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels prevMemory
    I32Div       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 `div` val1 -- TODO double check the order!!
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels prevMemory
    I32RemU      -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = (fromIntegral val2 :: Word32) `mod` (fromIntegral val1 :: Word32) -- TODO double check the order & also double check the result!!
                          in RuntimeContext (Push (fromIntegral result :: Int32) rest) prevLocals prevGlobal prevLabels prevMemory
    I32RemS      -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 `mod` val1 -- TODO double check the order!!
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels prevMemory
    I32EqZ       -> case prevStack of
                      Push val rest ->
                          let result = if val == 0 then (1 :: Int32) else (0 :: Int32)
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels prevMemory
    I32Eq        -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val1 == val2 then (1 :: Int32) else (0 :: Int32)
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels prevMemory

    I32Neq       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val1 /= val2 then (1 :: Int32) else (0 :: Int32)
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels prevMemory

    I32LtS       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 < val1 then (1 :: Int32) else (0 :: Int32)
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels prevMemory

    I32LtU       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if (fromIntegral val2 :: Word32) < (fromIntegral val1 :: Word32) then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels prevMemory

    I32LeS       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 <= val1 then (1 :: Int32) else (0 :: Int32)
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels prevMemory

    I32LeU       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if (fromIntegral val2 :: Word32) <= (fromIntegral val1 :: Word32) then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels prevMemory

    I32GtS       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 > val1 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels prevMemory
 
    I32GtU       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if (fromIntegral val2 :: Word32) > (fromIntegral val1 :: Word32) then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels prevMemory
 
    I32GeS       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 >= val1 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels prevMemory
 
    I32GeU       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if (fromIntegral val2 :: Word32) >= (fromIntegral val1 :: Word32) then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels prevMemory
 
    I64Add       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 + val1
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels prevMemory
 
    I64Sub       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 - val1 -- TODO double check the order!!
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels prevMemory
 
    I64Mul       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 * val1
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels prevMemory  
 
    I64Div       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 `div` val1 -- TODO double check the order!!
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels prevMemory
 
    I64RemU      -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = (fromIntegral val2 :: Word64) `mod` (fromIntegral val1 :: Word64) -- TODO double check the order & also double check the result!!
                          in RuntimeContext (Push (fromIntegral result :: Int64) rest) prevLocals prevGlobal prevLabels prevMemory
 
    I64RemS      -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 `mod` val1 -- TODO double check the order!!
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels prevMemory
 
    I64EqZ       -> case prevStack of
                      Push val rest ->
                          let result = if val == 0 then (1 :: Int64) else (0 :: Int64)
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels prevMemory
 
    I64Eq        -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val1 == val2 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels prevMemory
 
    I64Neq       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val1 /= val2 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels prevMemory
 
    I64LtS       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 < val1 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels prevMemory
 
    I64LtU       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if (fromIntegral val2 :: Word64) < (fromIntegral val1 :: Word64) then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels prevMemory
 
    I64LeS       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 <= val1 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels prevMemory
 
    I64LeU       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if (fromIntegral val2 :: Word64) <= (fromIntegral val1 :: Word64) then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels prevMemory
 
    I64GtS       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 > val1 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels prevMemory
 
    I64GtU       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if (fromIntegral val2 :: Word64) > (fromIntegral val1 :: Word64) then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels prevMemory
 
    I64GeS       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 >= val1 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels prevMemory
 
    I64GeU       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if (fromIntegral val2 :: Word64) >= (fromIntegral val1 :: Word64) then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels prevMemory
 
    Drop         -> case prevStack of
                      Push _ rest -> RuntimeContext rest prevLocals prevGlobal prevLabels prevMemory

    LocalGet idx -> case getLocalValue idx prevLocals of
                      val -> RuntimeContext (Push val prevStack) prevLocals prevGlobal prevLabels prevMemory

    LocalSet idx -> case prevStack of
                      Push val rest ->
                          let newLocals = setLocalValue idx val prevLocals
                          in RuntimeContext rest newLocals prevGlobal prevLabels prevMemory

    LocalTee idx -> case prevStack of
                      Push val rest ->
                          let newLocals = setLocalValue idx val prevLocals
                          in RuntimeContext (Push val rest) newLocals prevGlobal prevLabels prevMemory

    GlobalGet idx -> case getGlobalValue idx prevGlobal of
                      val -> RuntimeContext (Push val prevStack) prevLocals prevGlobal prevLabels prevMemory
    GlobalSet idx -> case prevStack of
                      Push val rest -> RuntimeContext rest prevLocals (setGlobalValue idx val prevGlobal) prevLabels prevMemory
    MemoryLoad @wasmType memIdx (SMemArg alignment offset) -> undefined
        -- let memArray = getMemoryArray memIdx prevMemory
        --     in case prevStack of
        --         Push i32addr restStack -> 
        --             let
        --                 inputAddr = fromIntegral i32addr
        --                 addr = fromIntegral (inputAddr + offset)
        --                 val = memArray !! addr 
        --                 in RuntimeContext (Push (val :: RuntimeTypeOf wasmType) restStack) prevLocals prevGlobal prevLabels prevMemory
                        -- in case val of
                        --     SomeWasmType (RInt32 loadedVal) -> RuntimeContext (Push (loadedVal :: RuntimeTypeOf wasmType) restStack) prevLocals prevGlobal prevLabels prevMemory :: RuntimeContext outputStack locals wasmModule inputLabels
                        --     SomeWasmType (RInt64 loadedVal) -> RuntimeContext (Push (loadedVal :: RuntimeTypeOf wasmType) restStack) prevLocals prevGlobal prevLabels prevMemory :: RuntimeContext outputStack locals wasmModule inputLabels
                        -- in RuntimeContext (Push val restStack) prevLocals prevGlobal prevLabels prevMemory :: RuntimeContext outputStack locals wasmModule inputLabels
    MemoryStore memIdx arg -> undefined
    Block (BTParamsResults _ (res :: KnownValStackShape resStack)) instrSeq -> 
        let newLabels = ConsLabels (Label (knownStackShapeLen res) (stackLength prevStack)) (labels prevCtxt)
            newContext =
                executeInstructionSequence instrSeq prevCtxt { labels = newLabels } -- :: RuntimeContext inputStack locals wasmModule ('(resStack, StackLength inputStack) :>: inputLabels)) 
        in newContext { labels = prevLabels } :: RuntimeContext outputStack locals wasmModule inputLabels
    Loop (BTParamsResults (params :: KnownValStackShape paramsStack) _) instrSeq -> 
        let newLabels = ConsLabels (Label (knownStackShapeLen params) (stackLength prevStack)) (labels prevCtxt)
            newContext = executeInstructionSequence instrSeq (prevCtxt { labels = newLabels } ) --untimeContext inputStack locals wasmModule ('(paramsStack, StackLength inputStack) :>: inputLabels)) 
        in newContext { labels = prevLabels } :: RuntimeContext outputStack locals wasmModule inputLabels
    If (BTParamsResults _ (res :: KnownValStackShape resStack)) thenSeq elseSeq -> case prevStack of
        Push cond (rest :: Stack inputStackWOCond) -> 
            if cond /= 0
            then 
                let newLabels = ConsLabels (Label (knownStackShapeLen res) (stackLength rest)) (labels prevCtxt)
                    newCtxt = executeInstructionSequence thenSeq (prevCtxt { labels = newLabels, stack = rest }) -- :: RuntimeContext inputStackWOCond locals wasmModule ('(resStack, StackLength inputStackWOCond) :>: inputLabels)) 
                in newCtxt { labels = prevLabels } -- :: RuntimeContext outputStack locals wasmModule inputLabels

            else 
                let newLabels = ConsLabels (Label (knownStackShapeLen res) (stackLength rest)) (labels prevCtxt)
                    newCtxt = executeInstructionSequence elseSeq (prevCtxt { labels = newLabels, stack = rest }) -- :: RuntimeContext inputStackWOCond locals wasmModule ('(resStack, StackLength inputStackWOCond) :>: inputLabels)) 
                in newCtxt { labels = prevLabels } -- :: RuntimeContext outputStack locals wasmModule inputLabels
    Br labelIdx -> 
        let Label labelType lenStackBeforeLabelCreation = getAtLabel labelIdx prevLabels
            (stackToKeep, _) = takeStack labelType prevStack
            baseStack  = reduceStackToLength lenStackBeforeLabelCreation prevStack
            finalStack = concatStacks stackToKeep baseStack
         in prevCtxt {
              stack = finalStack
             } :: RuntimeContext outputStack locals wasmModule inputLabels


    BrIf (labelIdx :: SFin i n) -> case prevStack of
        Push cond (rest :: Stack restStackShape) ->
            if cond == 0
            then prevCtxt { stack = rest } -- :: RuntimeContext restStackShape locals wasmModule inputLabels
            else prevCtxt { stack = rest
                          } --  :: RuntimeContext restStackShape locals wasmModule inputLabels


    Call funcName (FFuncTypeAnn params res) -> undefined -- executeFunction (Function Empty outputStack params (ConsLabels res prevLabels)) (RuntimeContext prevStack prevLocals prevGlobal prevLabels)
    Leave labelIdx -> undefined



executeInstructionSequence :: InstructionSequence inputStack outputStack locals wasmModule inputLabels outputLabels
                           -> RuntimeContext inputStack locals wasmModule inputLabels
                           -> RuntimeContext outputStack locals wasmModule outputLabels
                        --    -> RuntimeContext inputStack locals wasmModule (LenLabelStackShape inputLabels)
                        --    -> RuntimeContext outputStack locals wasmModule (LenLabelStackShape outputLabels)
executeInstructionSequence instrSeq prevCtxt@(RuntimeContext inputStack prevLocals prevWasmModule prevLabels prevMemory) = case instrSeq of
    End -> RuntimeContext inputStack prevLocals prevWasmModule prevLabels prevMemory
    (instr :| rest) ->
        let intermediateContext = executeInstruction instr prevCtxt
        in executeInstructionSequence rest intermediateContext

executeFunction :: Function inputStack outputStack locals labels wasmModule
                   -> RuntimeContext inputStack locals globals labels
                   -> RuntimeContext outputStack locals globals labels
                --    -> RuntimeContext inputStack locals globals (LenLabelStackShape labels)
                --    -> RuntimeContext outputStack locals globals (LenLabelStackShape labels)
executeFunction func@(Function (FFuncTypeAnn params res) instrSeq) prevCtxt = undefined
    -- let newCtxt = executeInstructionSequence instrSeq (prevCtxt { stack = EmptyStack, locals = params }) :: RuntimeContext Empty locals globals labels
    -- in newCtxt { stack = concatStacks res (stack prevCtxt) }



-- =============================================================================
-- Initializations
-- =============================================================================

