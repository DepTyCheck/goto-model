module Gens.Auto.Derivation.LinearBlock

import public Gens.Auto.Derivation.Common
import public Gens.Auto.Interface.LinearBlock

%logging "deptycheck.derive" 20

GenOrderTuning "RegOp".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [6]

GenOrderTuning "ProduceOp".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [15, 16, 17]

Gens.Auto.Interface.LinearBlock.genLinearBlock = deriveGen

