module Gens.Manual.Tree

import Data.Fin
import Data.Fuel
import Test.DepTyCheck.Gen
import Gens.Auto.Interface.Tree
import Gens.Manual.Numbers
import public Spec.Tree

genMaybeFin : (n : Nat) -> Gen MaybeEmpty $ MaybeFin n
genMaybeFin n = frequency [(1, pure Nothing), (1, Just <$> genFin n)]

minimumLeft : LTE a b -> minimum a b = a
minimumLeft LTEZero = Refl
minimumLeft (LTESucc prf') = cong S $ minimumLeft prf'

minimumRight : {a : _} -> {b : _} -> (LTE a b -> Void) -> minimum a b = b
minimumRight {a = a} {b = 0} f = rewrite minimumCommutative a 0 in Refl
minimumRight {a = 0} {b = (S b')} f = absurd $ f LTEZero
minimumRight {a = (S a')} {b = (S b')} f =
  let rec = minimumRight {a = a'} {b = b'} (f . LTESucc) in cong S $ rec

contraLte : {a : _} -> {b : _} -> (LTE a b -> Void) -> LT b a
contraLte {a = 0} {b = b} f = absurd $ f LTEZero
contraLte {a = (S a')} {b = 0} f = LTESucc LTEZero
contraLte {a = (S a')} {b = (S b')} f =
  let rec = contraLte {a = a'} {b = b'} (f . LTESucc) in LTESucc rec

decomposeLteMinimum : {a : _} -> {b : _} -> {c : _} ->
                      LTE a (minimum b c) -> (LTE a b, LTE a c)
decomposeLteMinimum x with (isLTE b c)
  decomposeLteMinimum x | (Yes prf) = do
    let leftRewrite = minimumLeft prf
    let leftPrf : LTE a b = rewrite sym $ leftRewrite in x
    (leftPrf, transitive leftPrf prf)
  decomposeLteMinimum x | (No contra) = do
    let rightRewrite = minimumRight contra
    let rightPrf : LTE a c = rewrite sym $ rightRewrite in x
    let transPrf = lteSuccLeft $ contraLte contra
    (transitive rightPrf transPrf, rightPrf)

public export
genPrimaryTree : (natSumF : Fuel) ->
                 (ovc : Nat) -> (vc : Nat) -> (lc : Nat) -> Gen MaybeEmpty $ PrimaryTree ovc vc lc
genPrimaryTree natSumF ovc vc lc with (isLTE lc vc)
  genPrimaryTree natSumF ovc 0 lc | (Yes prf) = empty
  genPrimaryTree natSumF ovc (S 0) 0 | (Yes LTEZero) = do
    x <- genFin ovc
    pure $ FakeLeaf x
  genPrimaryTree natSumF ovc (S 0) (S 0) | (Yes (LTESucc LTEZero)) = pure Leaf
  genPrimaryTree natSumF ovc (S (S k)) lc | (Yes prf) = do
    let node1Path = do
      edge <- genMaybeFin (ovc + (S k))
      subTree <- genPrimaryTree natSumF (S ovc) (S k) lc
      pure $ Node1 edge subTree
    let node2Path = do
      (leftVc ** rightVc ** vcPrf) <- genNatSum natSumF (S k)
      leftLcFin <- genFin $ S $ minimum leftVc lc
      let leftLcPrf' : ?
          leftLcPrf' = fromLteSucc $ finLT leftLcFin
      let leftLcPrf : ?
          leftLcPrf = snd $ decomposeLteMinimum leftLcPrf'
      let leftLc : ?
          leftLc = finToNat leftLcFin
      let (rightLc ** lcPrf) = getNatSumSecond leftLc lc @{leftLcPrf}
      leftTree <- genPrimaryTree natSumF (S $ ovc + rightVc) leftVc leftLc
      rightTree <- genPrimaryTree natSumF (S $ ovc + leftVc) rightVc rightLc
      pure $ Node2 leftTree rightTree @{vcPrf} @{lcPrf}
    frequency [(3, node1Path), (2, node2Path)]
  genPrimaryTree natSumF ovc vc lc | (No contra) = empty
  genPrimaryTree _ _ _ _ | (Yes prf) = empty  -- TODO: totality checker is broken. This has happened after case-split on prf

