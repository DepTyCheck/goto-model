module Gens.Auto.Interface.Program.Edges

import public Gens.Auto.Interface.Common
import public Spec.Program.Edges

public export
genEdgeDecision : Fuel
               -> {n, l : _}
               -> {ols : ListLoop n}
               -> {remSrcs : VectSource l n}
               -> (closeDec : CloseLoopDecision remSrcs ols)
               -> Gen MaybeEmpty $ EdgeDecision closeDec

