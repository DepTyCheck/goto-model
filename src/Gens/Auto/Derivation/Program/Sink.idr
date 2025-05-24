module Gens.Auto.Derivation.Program.Sink

import public Gens.Auto.Derivation.Common
import public Gens.Auto.Interface.Program.Sink

%logging "deptycheck.derive" 20

Gens.Auto.Interface.Program.Sink.genSink = deriveGen

