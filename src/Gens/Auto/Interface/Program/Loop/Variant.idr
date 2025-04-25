module Gens.Auto.Interface.Program.Loop.Variant

import public Gens.Auto.Interface.Common
import public Spec.Program.Loop.Variant

public export
genVariantDecision : Fuel ->
                     {n, l : _} ->
                     {b : _} ->
                     {a : VectSource l n} ->
                     (closeDec : CloseLoopDecision a b) ->
                     (finalRegs : VectValue n) ->
                     (canFinish : CanFinish closeDec finalRegs) ->
                     (edgeDec : EdgeDecision closeDec) ->
                     Gen MaybeEmpty $ VariantDecision closeDec finalRegs canFinish edgeDec

