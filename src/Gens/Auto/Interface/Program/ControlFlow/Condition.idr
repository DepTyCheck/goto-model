module Gens.Auto.Interface.Program.ControlFlow.Condition

import public Gens.Auto.Interface.Common
import public Spec.Program.ControlFlow.Decision.Condition

public export
genConditionDecision : Fuel ->
                       {n : _} ->
                       {l : _} ->
                       {a : VectSource l n} ->
                       {b : ListLoop n} ->
                       {regs : VectValue n} ->
                       {closeDec : CloseLoopDecision {n} a b} ->
                       {canFinish : CanFinish closeDec regs} ->
                       (edgeDec : EdgeDecision closeDec) ->
                       (varDec : VariantDecision closeDec regs canFinish edgeDec) ->
                       Gen MaybeEmpty $ ConditionDecision edgeDec varDec

