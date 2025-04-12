module Gens.Auto.Interface.Program.LinearBlock

import public Gens.Auto.Interface.Common
import public Spec.Program.LinearBlock
import public Show.Program.Raw
import public Show.Value

public export
genLinearBlock : Fuel ->
                 {n : _} -> (cLim : _) -> (regs : VectValue n) ->
                 Gen MaybeEmpty (finalRegs ** LinearBlock cLim regs finalRegs)

