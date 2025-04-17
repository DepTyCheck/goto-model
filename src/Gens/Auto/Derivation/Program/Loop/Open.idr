module Gens.Auto.Derivation.Program.Loop.Open

import public Gens.Auto.Derivation.Common
import public Gens.Auto.Interface.Program.Loop.Open

%logging "deptycheck.derive" 20

GenOrderTuning "AreWindedStep'".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [11, 10]

-- GenOrderTuning "OneNewLoop".dataCon where
--   isConstructor = itIsConstructor
--   deriveFirst _ _ = []

Gens.Auto.Interface.Program.Loop.Open.genOpenLoopDecision = deriveGen

