module Gens.Auto.Derivation.Edge

import public Gens.Auto.Derivation.Common
import public Gens.Auto.Interface.Edge

%logging "deptycheck.derive" 20

Gens.Auto.Interface.Edge.genEdgeDecision = deriveGen

