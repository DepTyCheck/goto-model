module Gens.Auto.Interface.Program.LinearBlock

import public Gens.Auto.Interface.Common
import public Spec.Program.LinearBlock

public export
genLinearBlock : Fuel
              -> {n, l : _}
              -> (cLim : _)
              -> {remSrcs : VectSource l n}
              -> {ols : ListLoop n}
              -> (closeDec : CloseLoopDecision {n} remSrcs ols)
              -> (regs : VectValue n)
              -> Gen MaybeEmpty (finalRegs ** LinearBlock cLim closeDec regs finalRegs)

