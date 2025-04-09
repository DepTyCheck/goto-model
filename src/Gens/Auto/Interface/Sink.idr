module Gens.Auto.Interface.Sink

import public Gens.Auto.Interface.Common
import public Spec.Program
import public Show.Program.Raw
import public Show.Value

public export
genSink : Fuel ->
          {m, n : _} -> (immSrc : MaybeSource n) -> (srcs : VectSource m n) ->
          Gen MaybeEmpty $ (bs ** SinkIsValid immSrc srcs bs)

