module Gens.Auto.Interface.Tree

import public Gens.Auto.Interface.Common
import public Spec.Tree


export
genStrongTree : Fuel ->
                (loc : Nat) ->
                (roc : Nat) ->
                (vc : Nat) ->
                (lc : Nat) ->
                Gen MaybeEmpty (PrimaryTree loc roc vc lc)
