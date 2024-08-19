module Gens.Manual.Numbers

import Decidable.Equality
import Data.Nat
import Data.Fin
import Test.DepTyCheck.Gen


public export
genFin : (n : Nat) -> Gen MaybeEmpty $ Fin n
genFin 0 = empty
genFin (S k) = elements' $ allFins (S k)

public export
genFin1 : (n : Nat) -> Gen NonEmpty $ Fin (S n)
-- TODO: add custom implementation

lemma : {a, b : _} -> (ltePrf : LTE a b) -> (eqContra : a = b -> Void) -> LT a b
lemma {a = 0} {b = 0} LTEZero eqContra = absurd $ eqContra Refl
lemma {a = 0} {b = (S k)} LTEZero eqContra = LTESucc LTEZero
lemma {a = S a'} {b = S b'} (LTESucc ltePrf') eqContra = LTESucc $ lemma {a = a'} {b = b'} ltePrf' (\eq' => eqContra $ cong S eq')

allNats' : (a : Nat) -> (b : Nat) -> (x : Nat) ->
           LTE a x => LTE x b =>
           List (c : Nat ** (LTE a c, LTE c b))
allNats' a b x @{axPrf} @{xbPrf} = case decEq b x of
                      (Yes Refl) => [(b ** (axPrf, xbPrf))]
                      (No contra) => let rec = allNats' a b (S x) @{lteSuccRight axPrf} @{lemma xbPrf (\eq => contra $ sym eq)} in (x ** (axPrf, xbPrf)) :: rec

allNats : (a : Nat) -> (b : Nat) -> List (c : Nat ** (LTE a c,  LTE c b))
allNats a b with (isLTE a b)
  allNats a b | (Yes prf) = allNats' a b a @{reflexive} @{prf}
  allNats a b | (No contra) = []

public export
genBoundedNat : (a : Nat) -> (b : Nat) -> Gen MaybeEmpty $ (c : Nat ** (LTE a c, LTE c b))
genBoundedNat a b = elements' $ allNats a b

