module WrongOtherLevel where

import Data.Singletons (Sing)
import Runtime.Interpreter
import Runtime.MemInst
import Runtime.Obligation
import Runtime.Stack
import Runtime.TableInst
import Runtime.Trap
import Syntax.Immediates
import Syntax.Instructions
import Syntax.Types
import Syntax.TypesIFC
import Validation.Shape

-- The step of a full-width load, as 'Runtime.Interpreter.stepInstr' has to write it: its result
-- is indexed by the load's check, @'BytesBelow level@.
loadStep ::
    (ModuleMems mod ~ (mem ': mems)) =>
    Store mod ->
    LocalSpaceInst locals ->
    Sing (level :: SecLevel) ->
    IsNum t ->
    MemArg ->
    ValueStack (('I32 ':~ la) ': s) ->
    Expr mod ('FrameShape locals ret) labels pcOut pcEnd ((t ':~ l) ': s) out ->
    Control mod res ret locals labels out ->
    Either Trap (StepResult ('BytesBelow level) mod res)
-- Wrong: compares the bytes with another level than the one the load declares.
loadStep store locals _ nt memArg (addr :# r) rest control =
    case loadChecked (currentMem store) SHigh (effectiveAddr addr memArg) (numBytes nt) of
        Left _ -> Left OutOfBoundsMemoryAccess
        Right checked -> Right (Stepped (BytesWereBelow checked) (Config store locals (loadValue nt (checkedWord checked) :# r) rest control))
