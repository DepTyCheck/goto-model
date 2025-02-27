module Gens.Auto.Derivation.Value

import public Gens.Auto.Derivation.Common
import public Gens.Auto.Interface.Value


%logging "deptycheck.derive" 5

Gens.Auto.Interface.Value.genRawValue0 = deriveGen
Gens.Auto.Interface.Value.genRawValue = deriveGen
Gens.Auto.Interface.Value.genVExpr01 = deriveGen
Gens.Auto.Interface.Value.genVExpr0 = deriveGen
Gens.Auto.Interface.Value.genVExpr = deriveGen
Gens.Auto.Interface.Value.genValue = deriveGen
