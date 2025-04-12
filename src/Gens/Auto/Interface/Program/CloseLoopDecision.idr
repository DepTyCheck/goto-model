module Gens.Auto.Interface.Program.CloseLoopDecision

import public Gens.Auto.Interface.Common
import public Spec.Program.Loop
import public Show.Program.Raw
import public Show.Value

public export
genCloseLoopDecision : Fuel ->
                       {n, l : _} -> (remSrcs : VectSource l n) -> (finalRegs : VectValue n) -> (ols : ListLoop n) ->
                       Gen MaybeEmpty $ CloseLoopDecision remSrcs finalRegs ols

