module Gens.Auto.Interface.Program.Sink

import public Gens.Auto.Interface.Common
import public Spec.Program.Sink
import public Show.Program.Raw
import public Show.Value

public export
genSink : Fuel ->
          {m, n : _} -> (immSrc : MaybeSource n) -> (srcs : VectSource m n) ->
          Gen MaybeEmpty $ (bs ** SinkIsValid immSrc srcs bs)

