module Gens.Auto.Derivation.Program.Loop.Variant

import public Gens.Auto.Derivation.Common
import public Gens.Auto.Interface.Program.Loop.Variant

%logging "deptycheck.derive" 20

-- TODO: gen order tuning for HasLoopVariant.Here

Gens.Auto.Interface.Program.Loop.Variant.genVariantDecision = deriveGen

