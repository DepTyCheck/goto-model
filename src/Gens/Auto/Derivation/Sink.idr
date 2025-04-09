module Gens.Auto.Derivation.Sink

import public Gens.Auto.Derivation.Common
import public Gens.Auto.Interface.Sink

%logging "deptycheck.derive" 20

Gens.Auto.Interface.Sink.genSink = deriveGen

