module Data.Nat.Extra


import Data.Nat


public export
minusLess : {a : Nat} -> {b : Nat} -> (LTE a b -> Void) -> b `minus` a = 0
minusLess {a = 0} {b = b} f = absurd (f LTEZero)
minusLess {a = (S a')} {b = 0} f = Refl
minusLess {a = (S a')} {b = (S b')} f = minusLess (f . LTESucc)

public export
minusLte : {a : Nat} -> {b : Nat} -> LTE (b `minus` a) b
minusLte with (isLTE a b)
  minusLte | (Yes LTEZero) = rewrite minusZeroRight b in reflexive
  minusLte {a = S a'} {b = S b'} | (Yes (LTESucc ltePrf')) = lteSuccRight minusLte
  minusLte | (No contra) = rewrite minusLess contra in LTEZero

