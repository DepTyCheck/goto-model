module Gens.Auto.Interface.CloseLoopDecision

import public Gens.Auto.Interface.Common
import public Spec.Program
import public Show.Program.Raw
import public Show.Value

public export
genCloseLoopDecision : Fuel ->
                       {n, l : _} -> (remSrcs : VectSource l n) -> (finalRegs : VectValue n) -> (ols : ListLoop n) ->
                       Gen MaybeEmpty $ CloseLoopDecision remSrcs finalRegs ols

