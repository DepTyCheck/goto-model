module Gens.Auto.Interface.Program.Loop.Open

import public Gens.Auto.Interface.Common
import public Spec.Program.Loop.Decision.Open

public export
genOpenLoopDecision : Fuel
                   -> {n : _}
                   -> (src : Source n)
                   -> (ols : ListLoop n)
                   -> (b : Bool)
                   -> Gen MaybeEmpty $ OpenLoopDecision src ols b

