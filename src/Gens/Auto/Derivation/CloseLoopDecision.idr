module Gens.Auto.Derivation.CloseLoopDecision

import public Gens.Auto.Derivation.Common
import public Gens.Auto.Interface.CloseLoopDecision

%logging "deptycheck.derive" 20

GenOrderTuning "AreWindedStep'".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [11, 10]

GenOrderTuning "CanUnwindAllStep".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [8, 7]

Gens.Auto.Interface.CloseLoopDecision.genCloseLoopDecision = deriveGen

