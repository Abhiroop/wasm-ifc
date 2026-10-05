module WrongIndirectCallUnchecked where

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
-- Wrong, for an indirect call: its result is indexed by @'CalleeWithin bound@, and continuing
-- without the checked table lookup presents no evidence for it.
indirectStep ::
    Config mod res ->
    Sing ('LabelledFuncType bound ps rs) ->
    Either Trap (StepResult ('CalleeWithin bound) mod res)
indirectStep next _ = Right (Stepped NothingToCheck next)
loadStep = undefined
