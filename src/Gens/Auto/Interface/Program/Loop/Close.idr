module Gens.Auto.Interface.Program.Loop.Close

import public Gens.Auto.Interface.Common
import public Spec.Program.Loop.Decision.Close

public export
genCloseLoopDecision : Fuel ->
                       {n, l : _} ->
                       (remSrcs : VectSource l n) ->
                       (ols : ListLoop n) ->
                       Gen MaybeEmpty $ CloseLoopDecision remSrcs ols

