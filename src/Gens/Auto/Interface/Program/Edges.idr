module Gens.Auto.Interface.Program.Edges

import public Gens.Auto.Interface.Common
import public Spec.Program.Edges

public export
genEdgeDecision : Fuel ->
                  (ls : MaybeBool) ->
                  Gen MaybeEmpty $ EdgeDecision ls

