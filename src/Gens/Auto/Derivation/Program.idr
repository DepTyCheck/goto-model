module Gens.Auto.Derivation.Program

import public Gens.Auto.Derivation.Common
import public Gens.Auto.Interface.Program

%logging "deptycheck.derive" 20

GenOrderTuning "RegOp".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [6]

GenOrderTuning "ProduceOp".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [10, 11, 12]

GenOrderTuning "Step".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [9, 10, 11, 12, 13, 14]

GenOrderTuning "CanUnwindAllStep".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [8, 7]

GenOrderTuning "AreWindedStep'".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [11, 10]

Gens.Auto.Interface.Program.genProgram = deriveGen

{-
Gens.Auto.Interface.Program.genSink = deriveGen
Gens.Auto.Interface.Program.genLinearBlock = deriveGen
Gens.Auto.Interface.Program.genPossible = deriveGen

