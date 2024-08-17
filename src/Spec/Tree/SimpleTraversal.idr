module Spec.Tree.SimpleTraversal

import Data.Nat.Order.Properties
import Data.Fin
import Data.Vect
import public Spec.Tree


public export
record TreeTraversalData (n : Nat) where
  constructor TTD

  currentIndex : Fin n
  subTreeSize : Fin n
  leftEdge : MaybeFin n
  rightEdge : MaybeFin n


finMinus : Fin n -> Fin n -> Fin n
finMinus x FZ = x
finMinus FZ (FS y) = FZ
finMinus (FS x) (FS y) = weaken $ finMinus x y

finPlus : {n : _} -> Fin n -> Fin n -> Fin n
finPlus x FZ = x
finPlus FZ (FS y) = FS y
finPlus (FS x) (FS y) = let rec = finPlus (weaken x) (FS y) in
  case strengthen rec of
       Nothing => rec
       (Just z) => FS z

natToFinSafe : {n : Nat} -> Nat -> Fin (S n)
natToFinSafe 0 = FZ
natToFinSafe (S k) = let rec = natToFinSafe k in case strengthen rec of
                                                      Nothing => rec
                                                      (Just x) => FS x

lteLemma : (a : Nat) -> (b : Nat) -> LTE a (b + a)
lteLemma 0 b = LTEZero
lteLemma (S k) b = let rec = lteLemma k b in rewrite sym $ plusSuccRightSucc b k in LTESucc rec


-- n - number of all vertices
-- n' : (S n') = n
-- s - size of the subtree with the root with index x (s doesn't include the root!)
-- x < s then (S i) + x
-- x >= s and (x - s) < i then x - s
-- x >= s and (x - s) >= i then 1 + (x - s) + s = S x
convertEdge : {n' : Nat} -> let n = S n' in (s : Fin n) -> (i : Fin n) -> MaybeFin n' -> MaybeFin n
convertEdge s i Nothing = Nothing
convertEdge {n' = 0} s i (Just x) = absurd x
convertEdge {n' = (S k)} s i (Just x) = do
  let xnat : Nat
      xnat = finToNat x
  let xPrf : ?
      xPrf = finLT x
  let snat : Nat
      snat = finToNat s
  let inat : Nat
      inat = finToNat i
  if xnat < snat
     then Just $ (finS i) `finPlus` (weaken x)
     else let diff : Nat
              diff = xnat `minus` snat in if diff < inat
        then Just $ natToFinLT diff @{lteSuccRight $ transitive (LTESucc $ minusLTE snat xnat) xPrf}
        else Just $ FS x

leftSumRule2 : NatSum leftLen rightLen len -> (x : Nat) -> x + len = x + rightLen + leftLen
leftSumRule2 sumPrf x = rewrite sym $ natSumIsSum sumPrf in
  rewrite plusCommutative leftLen rightLen in
    rewrite plusAssociative x rightLen leftLen in Refl

rightSumRule2 : NatSum leftLen rightLen len -> (x : Nat) -> x + len = x + leftLen + rightLen
rightSumRule2 sumPrf x = rewrite sym $ natSumIsSum sumPrf in
  rewrite sym $ plusAssociative x leftLen rightLen in Refl

leftSumRule1 : NatSum leftLen rightLen len -> (x : Nat) -> x + S len = S (x + rightLen + leftLen)
leftSumRule1 sumPrf x = let rec = leftSumRule2 sumPrf x in
  rewrite sym $ plusSuccRightSucc x len in cong S rec

rightSumRule1 : NatSum leftLen rightLen len -> (x : Nat) -> x + S len = S (x + leftLen + rightLen)
rightSumRule1 sumPrf x = let rec = rightSumRule2 sumPrf x in
  rewrite sym $ plusSuccRightSucc x len in cong S rec

head' : Vect k a -> GT k 0 => a  -- TODO: avoidable somehow conveniently?
head' (x :: xs) @{(LTESucc _)} = x

split : NatSum leftLen rightLen len -> Vect len a -> (Vect leftLen a, Vect rightLen a)
split NatSumBase xs = ([], xs)
split (NatSumStep sumPrf) (x :: xs) = let (ys, zs) = split sumPrf xs in (x :: ys, zs)

buildStdTraversalArray' : {ovc : _} -> {vc : _} ->
                          (tree :PrimaryTree ovc vc lc) ->
                          let n = ovc + vc in
                          Vect vc (Fin n) ->
                          Vect vc (TreeTraversalData n)
buildStdTraversalArray' Leaf [i] = [TTD i (rewrite plusCommutative ovc 1 in 0) Nothing Nothing]
buildStdTraversalArray' (FakeLeaf edge) [i] = [TTD i (rewrite plusCommutative ovc 1 in 0) (rewrite plusCommutative ovc 1 in convertEdge 0 (rewrite plusCommutative 1 ovc in i) (Just edge)) Nothing]
buildStdTraversalArray' {vc = S vc'} (Node1 edge tree) (i :: is) = do
  let tail = buildStdTraversalArray' tree (rewrite plusSuccRightSucc ovc vc' in is)
  let tailS : Fin ?
      tailS = natToFinLT vc' @{LTESucc $ lteLemma vc' ovc}
  (TTD i (rewrite sym $ plusSuccRightSucc ovc vc' in tailS) (Just $ head' is) (rewrite sym $ plusSuccRightSucc ovc vc' in convertEdge tailS (rewrite plusSuccRightSucc ovc vc' in i) edge))
    :: (rewrite sym $ plusSuccRightSucc ovc vc' in tail)
buildStdTraversalArray' {vc = S vc'} (Node2 leftTree rightTree @{vcPrf}) (i :: is) = do
  let (leftIs, rightIs) = split vcPrf is
  let leftArray : Vect ? (TreeTraversalData $ ovc + S vc') = rewrite leftSumRule1 vcPrf ovc in
        buildStdTraversalArray' leftTree (rewrite sym $ leftSumRule1 vcPrf ovc in leftIs)
  let rightArray : Vect ? (TreeTraversalData $ ovc + S vc') = rewrite rightSumRule1 vcPrf ovc in
        buildStdTraversalArray' rightTree (rewrite sym $ rightSumRule1 vcPrf ovc in rightIs)
  let tailS = natToFinLT vc' @{LTESucc $ lteLemma vc' ovc}
  (TTD i (rewrite sym $ plusSuccRightSucc ovc vc' in tailS) (Just $ currentIndex $ head' leftArray) (Just $ currentIndex $ head' rightArray))
    :: (rewrite cong (\x => Vect x $ TreeTraversalData (ovc + S vc')) $ sym $ natSumIsSum vcPrf in leftArray ++ rightArray)

simpleFinSum : {n, m : Nat} -> Fin (S n) -> Fin m -> Fin (n + m)
simpleFinSum {m = S m'} x FZ = rewrite sym $ plusSuccRightSucc n m' in weakenN m' x
simpleFinSum {m = S m'} x (FS y) = rewrite sym $ plusSuccRightSucc n m' in FS $ simpleFinSum x y

public export
buildStdTraversalArray : {ovc : _} -> {vc : _} ->
                         (tree : PrimaryTree ovc vc lc) ->
                         (rootIndex : Fin (S ovc)) ->
                         Vect vc (TreeTraversalData (ovc + vc))
buildStdTraversalArray tree rootI = buildStdTraversalArray' tree $ (simpleFinSum rootI) <$> allFins vc

public export
buildStdTraversalArray1 : {ovc : _} -> {vc' : _} ->
                          (tree : PrimaryTree ovc (S vc') lc) ->
                          (rootIndex : Fin (S ovc)) ->
                          Vect (S vc') (TreeTraversalData (S $ ovc + vc'))
buildStdTraversalArray1 = rewrite plusSuccRightSucc ovc vc' in buildStdTraversalArray

