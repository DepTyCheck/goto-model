module Gens.Auto.Derivation.Program

import public Gens.Auto.Interface
import Deriving.DepTyCheck.Gen


%default total
%logging "deptycheck.derive" 5


Gens.Auto.Interface.genStrongTree = deriveGen
