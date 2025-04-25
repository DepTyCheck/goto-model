module Gens.Auto.Interface.Program.ControlFlow.Condition

import public Gens.Auto.Interface.Common
import public Spec.Program.ControlFlow.Decision.Condition

public export
genConditionDecision : Fuel ->
                       {closeDec : CloseLoopDecision a b} ->
                       {canFinish : CanFinish closeDec regs} ->
                       (edgeDec : EdgeDecision closeDec) ->
                       (varDec : VariantDecision closeDec regs canFinish edgeDec) ->
                       Gen MaybeEmpty $ ConditionDecision edgeDec varDec

