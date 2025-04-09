module Gens.Auto.Interface.Loop

import public Gens.Auto.Interface.Common
import public Spec.Program
import public Show.Program.Raw
import public Show.Value

public export
genLoopDecision : Fuel ->
                  {n : _} -> (src : Source n) -> (ols : ListLoop n) ->
                  Gen MaybeEmpty $ LoopDecision src ols

public export
genCloseLoopDecision : Fuel ->
                       {n, l : _} -> (remSrcs : VectSource l n) -> (finalRegs : VectValue n) -> (ols : ListLoop n) ->
                       Gen MaybeEmpty $ CloseLoopDecision remSrcs finalRegs ols

