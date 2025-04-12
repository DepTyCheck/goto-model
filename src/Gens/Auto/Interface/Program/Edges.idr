module Gens.Auto.Interface.Program.Edges

import public Gens.Auto.Interface.Common
import public Spec.Program.Edges
import public Show.Program.Raw
import public Show.Value

public export
genEdgeDecision : Fuel ->
                  (ls : MaybeBool) ->
                  Gen MaybeEmpty $ EdgeDecision ls

