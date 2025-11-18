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
import Data.Word (Word32)
import Types (RuntimeTypeOf, ValStackShape(..), type (+>+), GetLabelType, LabelStackShape(..), RemoveLabels, BlockType (..), SValStackShape(..), FuncTypeAnn (..), StackLength, stackShapeLen, Take, Drop, GetLabelCreationStackLength, FuncTypeAnn (..), Reverse)
import Utils
import WasmModule (WasmModule(..), GetGlobals, GlobalTypeToWasmType, GlobalsShape, GlobalType (GlobalTypeMW), KnownMutability(SVar, SConst))
import Wasm
{-
=============================================================================
INTERPRETER
=============================================================================
-}

-- | Runtime representation of the WebAssembly stack.
-- This is the actual data structure that holds stack values during execution.
data Stack (stackShape :: ValStackShape) where
    EmptyStack :: Stack EmptyValStack
    Push       :: RuntimeTypeOf wasmType -> Stack stackShape -> Stack (wasmType :> stackShape)

stackLength :: Stack stackShape -> SNat (StackLength stackShape)
stackLength EmptyStack       = SZ
stackLength (Push _ rest) = SS (stackLength rest)


takeStack :: SNat n -> Stack s -> (Stack (Take n s), Stack (Drop n s))
takeStack SZ stk = (EmptyStack, stk)
takeStack (SS n) (Push x xs) =
  let (taken, rest) = takeStack n xs
  in (Push x taken, rest)



concatStacks :: Stack s1 -> Stack s2 -> Stack (s1 +>+ s2)
concatStacks EmptyStack s2       = s2
concatStacks (Push val rest) s2 = Push val (concatStacks rest s2)


popNthLabel :: ( GetLabelCreationStackLength n restLabelsShape ~ stackLen
               , GetLabelType n restLabelsShape ~ rightLabelStack) =>
               SFin n l
            -> Labels restLabelsShape
            -> (SValStackShape rightLabelStack, SNat stackLen)
popNthLabel SFZ (ConsLabels sstackShape lenInputStack _) = (sstackShape, lenInputStack)
popNthLabel (SFS idx) (ConsLabels _ _ rest) = popNthLabel idx rest
popNthLabel _ NoLabels = error "Index out of bounds in popNthLabel"


reduceStackToLength :: forall n stackShape.
                       SNat n
                    -> Stack stackShape
                    -> Stack (Take n (Reverse stackShape))
reduceStackToLength n = fst . takeStack n . reverseStack

reverseStack :: Stack stackShape -> Stack (Reverse stackShape)
reverseStack EmptyStack = EmptyStack
reverseStack (Push @wasmType val rest) =
  concatStacks (reverseStack rest) (Push @wasmType val EmptyStack)


removeLabelsUntilStackIdx :: forall n l (inputLabelStack :: LabelStackShape l). SFin n l -> Labels inputLabelStack -> Labels (RemoveLabels n inputLabelStack)
removeLabelsUntilStackIdx SFZ (ConsLabels _ _ rest) = rest
removeLabelsUntilStackIdx (SFS idx) (ConsLabels _ _ rest) = removeLabelsUntilStackIdx idx rest



-- | Runtime representation of the WebAssembly locals.
-- This is the actual data structure that holds local values during execution.
data Locals (localsShape :: LocalsShape n) where
    NoLocals   :: Locals 'VNil
    ConsLocals :: RuntimeTypeOf wasmType -> Locals localsShape -> Locals (wasmType :<| localsShape)

data Globals (globalsShape :: GlobalsShape n) where
    NoGlobals   :: Globals 'VNil
    ConsGlobals :: RuntimeTypeOf wasmType -> KnownMutability m -> Globals globalsShape -> Globals (GlobalTypeMW m wasmType :<| globalsShape)

data Labels (labelsShape :: LabelStackShape n) where
    NoLabels :: Labels 'Types.EmptyLabels
    ConsLabels  :: SValStackShape labelStackShape -> SNat m -> Labels restLabelsShape -> Labels ('(labelStackShape, m) :>: restLabelsShape)
-- data Memory (memsShape :: MemoriesShape n) where
--     NoMems   :: Memory 'VNil
--     ConsMems :: MemoryType -> Memory memsShape -> Memory (MemoryType :<| memsShape)


data RuntimeContext (stackShape :: ValStackShape) (localsShape :: LocalsShape n) (wasmModule :: WasmModule shape) (labelsShape :: LabelStackShape m) = RuntimeContext
    { stack  :: Stack stackShape,
      locals :: Locals localsShape,
      globals :: Globals (GetGlobals wasmModule), -- :: GlobalsShape (GetGlobalsShape shape)),
      labels :: Labels labelsShape
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

-- TODO
executeInstruction :: forall inputStack outputStack locals wasmModule inputLabels outputLabels .
                      Instruction inputStack outputStack locals wasmModule inputLabels outputLabels
                   -> RuntimeContext inputStack locals wasmModule inputLabels
                   -> RuntimeContext outputStack locals wasmModule outputLabels
executeInstruction instr prevCtxt@(RuntimeContext prevStack prevLocals prevGlobal prevLabels) = case instr of
    I32Const val -> RuntimeContext (Push val prevStack) prevLocals prevGlobal prevLabels
    I32Add       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 + val1
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
    I32Sub       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val1 - val2 -- TODO double check the order!!
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels 
    I32Mul       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 * val1
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
    I32Div       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 `div` val1 -- TODO double check the order!!
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
    I32RemU      -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = (fromIntegral val2 :: Word32) `mod` (fromIntegral val1 :: Word32) -- TODO double check the order & also double check the result!!
                          in RuntimeContext (Push (fromIntegral result :: Int32) rest) prevLocals prevGlobal prevLabels
    I32RemS      -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 `mod` val1 -- TODO double check the order!!
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
    I32EqZ       -> case prevStack of
                      Push val rest ->
                          let result = if val == 0 then (1 :: Int32) else (0 :: Int32)
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
    I32Eq        -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val1 == val2 then (1 :: Int32) else (0 :: Int32)
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels

    I32Neq       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val1 /= val2 then (1 :: Int32) else (0 :: Int32)
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels

    I32LtS       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 < val1 then (1 :: Int32) else (0 :: Int32)
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels

    I32LtU       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if (fromIntegral val2 :: Word32) < (fromIntegral val1 :: Word32) then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels

    I32LeS       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 <= val1 then (1 :: Int32) else (0 :: Int32)
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels

    I32LeU       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if (fromIntegral val2 :: Word32) <= (fromIntegral val1 :: Word32) then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels

    I32GtS       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 > val1 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I32GtU       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if (fromIntegral val2 :: Word32) > (fromIntegral val1 :: Word32) then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I32GeS       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 >= val1 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I32GeU       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if (fromIntegral val2 :: Word32) >= (fromIntegral val1 :: Word32) then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I64Add       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 + val1
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I64Sub       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 - val1 -- TODO double check the order!!
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I64Mul       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 * val1
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I64Div       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 `div` val1 -- TODO double check the order!!
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I64RemU      -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = (fromIntegral val2 :: Word64) `mod` (fromIntegral val1 :: Word64) -- TODO double check the order & also double check the result!!
                          in RuntimeContext (Push (fromIntegral result :: Int64) rest) prevLocals prevGlobal prevLabels
 
    I64RemS      -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 `mod` val1 -- TODO double check the order!!
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I64EqZ       -> case prevStack of
                      Push val rest ->
                          let result = if val == 0 then (1 :: Int64) else (0 :: Int64)
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I64Eq        -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val1 == val2 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I64Neq       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val1 /= val2 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I64LtS       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 < val1 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I64LtU       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if (fromIntegral val2 :: Word64) < (fromIntegral val1 :: Word64) then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I64LeS       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 <= val1 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I64LeU       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if (fromIntegral val2 :: Word64) <= (fromIntegral val1 :: Word64) then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I64GtS       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 > val1 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I64GtU       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if (fromIntegral val2 :: Word64) > (fromIntegral val1 :: Word64) then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I64GeS       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 >= val1 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I64GeU       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if (fromIntegral val2 :: Word64) >= (fromIntegral val1 :: Word64) then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    Drop         -> case prevStack of
                      Push _ rest -> RuntimeContext rest prevLocals prevGlobal prevLabels

    LocalGet idx -> case getLocalValue idx prevLocals of
                      val -> RuntimeContext (Push val prevStack) prevLocals prevGlobal prevLabels

    LocalSet idx -> case prevStack of
                      Push val rest ->
                          let newLocals = setLocalValue idx val prevLocals
                          in RuntimeContext rest newLocals prevGlobal prevLabels

    LocalTee idx -> case prevStack of
                      Push val rest ->
                          let newLocals = setLocalValue idx val prevLocals
                          in RuntimeContext (Push val rest) newLocals prevGlobal prevLabels

    GlobalGet idx -> case getGlobalValue idx prevGlobal of
                      val -> RuntimeContext (Push val prevStack) prevLocals prevGlobal prevLabels
    GlobalSet idx -> case prevStack of
                      Push val rest -> RuntimeContext rest prevLocals (setGlobalValue idx val prevGlobal) prevLabels
    MemoryLoad arg -> undefined
    MemoryStore arg -> undefined
    Block (BTParamsResults _ (res :: SValStackShape resStack)) instrSeq ->
      let newLabels = ConsLabels res (stackLength prevStack) (labels prevCtxt)
          newContext =
            executeInstructionSequence instrSeq (prevCtxt { labels = newLabels } :: RuntimeContext inputStack locals wasmModule ('(resStack, StackLength inputStack) :>: inputLabels)) funcMap
      in newContext { labels = prevLabels } :: RuntimeContext outputStack locals wasmModule inputLabels
    Loop (BTParamsResults (params :: SValStackShape paramsStack) _) instrSeq -> 
                let newLabels = ConsLabels params (stackLength prevStack) (labels prevCtxt)
                    newContext = executeInstructionSequence instrSeq (prevCtxt { labels = newLabels } :: RuntimeContext inputStack locals wasmModule ('(paramsStack, StackLength inputStack) :>: inputLabels)) funcMap
                in newContext { labels = prevLabels }
    If (BTParamsResults _ (res :: SValStackShape resStack)) thenSeq elseSeq -> case prevStack of
        Push cond (rest :: Stack inputStackWOCond) ->
            if cond /= 0
            then 
                let newLabels = ConsLabels res (stackLength rest) (labels prevCtxt)
                    newCtxt = executeInstructionSequence thenSeq (prevCtxt { labels = newLabels, stack = rest } :: RuntimeContext inputStackWOCond locals wasmModule ('(resStack, StackLength inputStackWOCond) :>: inputLabels)) funcMap
                in newCtxt { labels = prevLabels } :: RuntimeContext outputStack locals wasmModule inputLabels

            else 
                let newLabels = ConsLabels res (stackLength rest) (labels prevCtxt)
                    newCtxt = executeInstructionSequence elseSeq (prevCtxt { labels = newLabels, stack = rest } :: RuntimeContext inputStackWOCond locals wasmModule ('(resStack, StackLength inputStackWOCond) :>: inputLabels)) funcMap
                in newCtxt { labels = prevLabels } :: RuntimeContext outputStack locals wasmModule inputLabels
    Br (labelIdx :: SFin i n) ->
        let (labelType, lenStackBeforeLabelCreation) = popNthLabel labelIdx prevLabels
            (stackToKeep, _) = takeStack (stackShapeLen labelType) prevStack
            baseStack  = reduceStackToLength lenStackBeforeLabelCreation prevStack
            finalStack = concatStacks stackToKeep baseStack
         in prevCtxt {
              stack = finalStack
             }  :: RuntimeContext outputStack locals wasmModule inputLabels

    BrIf (labelIdx :: SFin i n) -> case prevStack of
        Push cond (rest :: Stack restStackShape) ->
            -- if cond == 0
            -- then prevCtxt { stack = rest } :: RuntimeContext outputStack locals wasmModule inputLabels
            -- else
                let (labelType, lenStackBeforeLabelCreation) = popNthLabel labelIdx prevLabels
                    (stackToKeep, _) = takeStack (stackShapeLen labelType) rest
                    baseStack  = reduceStackToLength lenStackBeforeLabelCreation rest
                    finalStack = concatStacks stackToKeep baseStack
                in prevCtxt {
                    stack = finalStack
                    }  :: RuntimeContext outputStack locals wasmModule inputLabels
    Call funcName (FFuncTypeAnn params res) -> undefined -- executeFunction (Function Empty outputStack params (ConsLabels res prevLabels)) (RuntimeContext prevStack prevLocals prevGlobal prevLabels)

executeInstructionSequence :: InstructionSequence inputStack outputStack locals wasmModule inputLabels inputLabels
                           -> RuntimeContext inputStack locals wasmModule inputLabels
                           -> RuntimeContext outputStack locals wasmModule inputLabels
executeInstructionSequence instrSeq prevCtxt@(RuntimeContext inputStack prevLocals prevWasmModule prevLabels) = case instrSeq of
    End -> RuntimeContext inputStack prevLocals prevWasmModule prevLabels
    (instr :| rest) ->
        let intermediateContext = executeInstruction instr prevCtxt
        in executeInstructionSequence rest intermediateContext

executeFunction :: Function inputStack outputStack locals labels
                   -> RuntimeContext inputStack locals globals labels
                   -> RuntimeContext outputStack locals globals labels
executeFunction func@(Function (FFuncTypeAnn params res) instrSeq) prevCtxt = undefined
    -- let newCtxt = executeInstructionSequence instrSeq (prevCtxt { stack = EmptyStack, locals = params }) :: RuntimeContext Empty locals globals labels
    -- in newCtxt { stack = concatStacks res (stack prevCtxt) }
