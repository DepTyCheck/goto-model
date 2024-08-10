module Gens.Auto.Interface.Program

import public Gens.Auto.Interface.Common
import public Spec.Program


export
genStrongTree : Fuel ->
                (loc : Nat) ->
                (roc : Nat) ->
                (vc : Nat) ->
                (lc : Nat) ->
                Gen MaybeEmpty (PrimaryTree loc roc vc lc)
