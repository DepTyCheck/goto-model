module Gens.Auto.Interface.Program.ControlFlow.Edge

import public Gens.Auto.Interface.Common
import public Spec.Program.ControlFlow.Decision.Edge

public export
genEdgeDecision : Fuel
               -> {n, l : _}
               -> {ols : ListLoop n}
               -> {remSrcs : VectSource l n}
               -> (closeDec : CloseLoopDecision remSrcs ols)
               -> Gen MaybeEmpty $ EdgeDecision closeDec

