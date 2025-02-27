module Gens.Auto.Derivation.Program

import public Gens.Auto.Derivation.Common
import public Gens.Auto.Interface.Program
import Spec.Value.Decidable
import Spec.Context.Decidable


%logging "deptycheck.derive" 20


{-
-- n fs uc ols contRegs regs target i Duplicate Program
-- 0  1  2   3        4    5      6 7         8       9
GenOrderTuning "Assign".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [8]
-}

GenOrderTuning "RegOp".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = []

GenOrderTuning "Source1".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [4, 5]

GenOrderTuning "Source2".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [5, 6, 7]

Gens.Auto.Interface.Program.genProgram = deriveGen
