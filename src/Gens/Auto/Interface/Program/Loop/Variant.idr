module Gens.Auto.Interface.Program.Loop.Variant

import public Gens.Auto.Interface.Common
import public Spec.Program.Loop.Variant

public export
genVariantDecision : Fuel ->
                     (closeDec : CloseLoopDecision a b) ->
                     (finalRegs : VectValue n) ->
                     (edgeDec : EdgeDecision closeDec) ->
                     Gen MaybeEmpty $ VariantDecision closeDec finalRegs edgeDec

