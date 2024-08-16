module Gens.Auto.Interface.Tree

import public Gens.Auto.Interface.Common
import public Spec.Tree


public export
genNatSum : Fuel ->
            (c : Nat) -> Gen MaybeEmpty (a ** b ** NatSum a b c)
