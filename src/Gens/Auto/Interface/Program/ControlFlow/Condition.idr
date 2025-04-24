module Gens.Auto.Interface.Program.ControlFlow.Condition

import public Gens.Auto.Interface.Common
import public Spec.Program.ControlFlow.Decision.Condition

public export
genConditionDecision : Fuel ->
                       {closeDec : CloseLoopDecision a b} ->
                       (edgeDec : EdgeDecision closeDec) ->
                       (varDec : VariantDecision closeDec regs edgeDec) ->
                       Gen MaybeEmpty $ ConditionDecision edgeDec varDec

