module Gens.Manual.Numbers

import Data.Fin
import Test.DepTyCheck.Gen


public export
genFin : (n : Nat) -> Gen MaybeEmpty $ Fin n
genFin 0 = empty
genFin (S k) = elements' $ allFins (S k)

public export
genFin1 : (n : Nat) -> Gen NonEmpty $ Fin (S n)
-- TODO: add custom implementation

