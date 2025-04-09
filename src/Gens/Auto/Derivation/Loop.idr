module Gens.Auto.Derivation.Loop

import public Gens.Auto.Derivation.Common
import public Gens.Auto.Interface.Loop

%logging "deptycheck.derive" 20

GenOrderTuning "CanUnwindAllStep".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [8, 7]

GenOrderTuning "AreWindedStep'".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [11, 10]

Gens.Auto.Interface.Loop.genLoopDecision = deriveGen
Gens.Auto.Interface.Loop.genCloseLoopDecision = deriveGen

