module Gens.Auto.Derivation.Program

import public Gens.Auto.Derivation.Common
import public Gens.Auto.Interface.Program
import Spec.Value.Decidable
import Spec.Context.Decidable


%logging "deptycheck.derive" 20


-- n fs uc ols contRegs regs target i Duplicate Program
-- 0  1  2   3        4    5      6 7         8       9
GenOrderTuning "Assign".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [8]


-- n fs uc ols contRegs regs contV rv lv vop target li ri (Index li) (Index ri) Produce ReplaceAt Program
--                                                  11 12    13          14        15       16     17
GenOrderTuning "RegOp".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [13, 14, 15, 16]

-- n contFs contRegs contUc contOls fs regs uc ols ForwardEdge Program
-- 0      1        2      3       4  5    6  7   8           9      10
GenOrderTuning "Source1".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [3]

GenOrderTuning "Source2".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [4, 5]

Gens.Auto.Interface.Program.genProgram = deriveGen
