module Gens.Auto.Interface.Program


import public Gens.Auto.Interface.Common
import public Spec.Program


public export
genProgram : Fuel -> {n : _} -> (ctx : Context n) -> Gen MaybeEmpty (Program ctx)
