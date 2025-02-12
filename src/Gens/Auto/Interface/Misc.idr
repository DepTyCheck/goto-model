module Gens.Auto.Interface.Misc


import public Gens.Auto.Interface.Common
import public Spec.Misc


public export
genBoolAnd012 : Fuel -> Gen MaybeEmpty $ (a ** b ** c ** BoolAnd a b c)

public export
genBoolAnd0 : Fuel -> (a : _) -> Gen MaybeEmpty $ (b ** c ** BoolAnd a b c)

public export
genBoolAnd1 : Fuel -> (b : _) -> Gen MaybeEmpty $ (a ** c ** BoolAnd a b c)

public export
genBoolAnd2 : Fuel -> (c : _) -> Gen MaybeEmpty $ (a ** b ** BoolAnd a b c)

public export
genNotSame01 : Fuel -> (a, b : _) -> Gen MaybeEmpty $ NotSame a b

