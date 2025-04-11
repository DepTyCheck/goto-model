module Gens.Auto.Interface.LoopDecision

import public Gens.Auto.Interface.Common
import public Spec.Program
import public Show.Program.Raw
import public Show.Value

public export
genLoopDecision : Fuel ->
                  {n : _} -> (src : Source n) -> (ols : ListLoop n) ->
                  Gen MaybeEmpty $ LoopDecision src ols

