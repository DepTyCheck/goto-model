module Gens.Auto.Interface.Edge

import public Gens.Auto.Interface.Common
import public Spec.Program
import public Show.Program.Raw
import public Show.Value

public export
genEdgeDecision : Fuel ->
                  (ls : MaybeBool) ->
                  Gen MaybeEmpty $ EdgeDecision ls

