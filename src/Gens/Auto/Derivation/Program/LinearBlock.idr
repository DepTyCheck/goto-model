module Gens.Auto.Derivation.Program.LinearBlock

import public Gens.Auto.Derivation.Common
import public Gens.Auto.Interface.Program.LinearBlock

%logging "deptycheck.derive" 20

GenOrderTuning "Assign".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [10, 11]

GenOrderTuning "RegOp".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [11, 12]

GenOrderTuning "ProduceOp".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [15, 16, 17]

Gens.Auto.Interface.Program.LinearBlock.genLinearBlock = deriveGen

