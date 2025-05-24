module Gens.Auto.Derivation.Program

import public Gens.Auto.Derivation.Common
import public Gens.Auto.Interface.Program

%logging "deptycheck.derive" 20

GenOrderTuning "Step".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [10, 11, 12, 13, 14, 15]

Gens.Auto.Interface.Program.genProgram = deriveGen

