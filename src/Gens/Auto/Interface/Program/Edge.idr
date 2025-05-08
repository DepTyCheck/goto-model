module Gens.Auto.Interface.Program.Edge

import public Gens.Auto.Interface.Common
import public Spec.Program.Edge

public export
genEdgeDecision : Fuel ->
                  {n, l : _} ->
                  {ols : ListLoop n} ->
                  {remSrcs : VectSource l n} ->
                  (closeDec : CloseLoopDecision remSrcs ols) ->
                  (finalRegs : VectValue n) ->
                  (canFinish : CanFinish closeDec finalRegs) ->
                  Gen MaybeEmpty $ EdgeDecision closeDec finalRegs canFinish

