module Gens.Auto.Interface.Tree

import public Gens.Auto.Interface.Common
import public Spec.Tree


public export
genNatSum : Fuel ->
            (c : Nat) -> Gen MaybeEmpty (a ** b ** NatSum a b c)

{-
public export
genProportion : Fuel ->
                (k : Nat) -> (x : Nat) ->
                Gen MaybeEmpty (l : SnocVectNat k ** l `SumsTo` x)
-}

public export
genAbstractTree : Fuel ->
                  (ps : Params) -> Gen MaybeEmpty $ AbstractTree ps

