module Gens.Auto.Interface.Program.LinearBlock

import public Gens.Auto.Interface.Common
import public Spec.Program.LinearBlock

public export
genLinearBlock : Fuel ->
                 {n : _} -> (cLim : _) -> (ols : ListLoop n) -> (regs : VectValue n) ->
                 Gen MaybeEmpty (finalRegs ** LinearBlock cLim ols regs finalRegs)

