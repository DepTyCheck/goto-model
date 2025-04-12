module Gens.Auto.Interface.Program.LoopDecision

import public Gens.Auto.Interface.Common
import public Spec.Program.Loop

public export
genLoopDecision : Fuel ->
                  {n : _} -> (src : Source n) -> (ols : ListLoop n) ->
                  Gen MaybeEmpty $ LoopDecision src ols

