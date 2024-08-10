module Gens.Auto.Interface


import public Spec.Program
import public Data.Fuel
import public Test.DepTyCheck.Gen


export
genStrongTree : Fuel ->
                (loc : Nat) ->
                (roc : Nat) ->
                (vc : Nat) ->
                (lc : Nat) ->
                Gen MaybeEmpty (PrimaryTree loc roc vc lc)
