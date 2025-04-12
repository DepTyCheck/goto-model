module Gens.Auto.Derivation.Program.LoopDecision

import public Gens.Auto.Derivation.Common
import public Gens.Auto.Interface.Program.LoopDecision

%logging "deptycheck.derive" 20

GenOrderTuning "AreWindedStep'".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [11, 10]

Gens.Auto.Interface.Program.LoopDecision.genLoopDecision = deriveGen

