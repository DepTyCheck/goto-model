module Spec.Tree.Traversal

import Control.Monad.State
import Data.Nat.Order.Properties
import Data.Fin
import Data.Vect
import public Spec.Tree


public export
record TreeTraversalData (n : Nat) where
  constructor TTD

  currentIndexPair : IndexPair n
  leftEdge : MaybeFin n
  rightEdge : MaybeFin n

finIdentity : {x : Nat} -> {b : Nat} -> (prf : LT x b) -> finToNat (natToFinLT x @{prf}) = x
finIdentity {b = S b'} (LTESucc prf') = ?finIdentity_rhs_0

minusPlus'' : (n : Nat) -> (m : Nat) -> minus (plus m n) m = n
minusPlus'' n 0 = rewrite minusZeroRight n in Refl
minusPlus'' n (S k) = minusPlus'' n k

minusPlus' : (n : Nat) -> (m : Nat) -> minus (plus n m) m = n
minusPlus' n m = rewrite plusCommutative n m in minusPlus'' n m

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

lteLemma : (a : Nat) -> (b : Nat) -> LTE a (b + a)
lteLemma 0 b = LTEZero
lteLemma (S k) b = let rec = lteLemma k b in rewrite sym $ plusSuccRightSucc b k in LTESucc rec

buildIndices : {ovc : _} -> {vc : _} ->
               (tree : PrimaryTree ovc vc lc) ->
               (rootIndex : Fin $ S ovc) ->
               Vect vc $ IndexPair (ovc + vc) 
buildIndices Leaf rootI = rewrite plusCommutative ovc 1 in [(FZ ** rootI)]
buildIndices (FakeLeaf edge) rootI = rewrite plusCommutative ovc 1 in [(FZ ** rootI)]
buildIndices {vc = S vc'} (Node1 edge tree) rootI = do
  let tail = buildIndices tree (FS rootI)
  let finPrf : ?
      finPrf = LTESucc $ lteLemma vc' ovc
  (rewrite sym $ plusSuccRightSucc ovc vc' in (natToFinLT vc' @{finPrf} ** rewrite finIdentity {x = vc'} finPrf in rewrite minusPlus' (S ovc) vc' in rootI) :: tail)
buildIndices {vc = S vc'} (Node2 {leftVc} {rightVc} leftTree rightTree @{vcPrf}) rootI = do
  let leftPart : Vect leftVc (IndexPair $ ovc + S vc') = rewrite leftSumRule1 vcPrf ovc in buildIndices leftTree (weakenN rightVc $ FS rootI)
  let rightPart : Vect rightVc (IndexPair $ ovc + S vc') = rewrite rightSumRule1 vcPrf ovc in buildIndices rightTree (rewrite plusSuccRightSucc ovc leftVc in ?hole $ FS $ shift leftVc $ rootI)
  let finPrf : ?
      finPrf = lteLemma (S vc') ovc
  (natToFinLT vc' @{finPrf} ** rewrite finIdentity {x = vc'} finPrf in rewrite sym $ plusSuccRightSucc ovc vc' in rewrite minusPlus' (S ovc) vc' in rootI) :: (rewrite cong (\x => Vect x (IndexPair $ ovc + S vc')) $ sym $ natSumIsSum vcPrf in leftPart ++ rightPart)

split : NatSum leftLen rightLen len -> Vect len a -> (Vect leftLen a, Vect rightLen a)
split NatSumBase xs = ([], xs)
split (NatSumStep sumPrf) (x :: xs) = let (ys, zs) = split sumPrf xs in (x :: ys, zs)

buildStdTraversalArray' : {ovc : _} -> {vc : _} ->  -- TODO: implicits are everywhere
                          (tree : PrimaryTree ovc vc lc) ->
                          let n = ovc + vc in
                          Vect vc (IndexPair n) ->
                          Vect vc (TreeTraversalData n)
buildStdTraversalArray' Leaf [ip] = [TTD ip Nothing Nothing]
buildStdTraversalArray' (FakeLeaf edge) [ip] = [TTD ip (rewrite plusCommutative ovc 1 in convertEdge (rewrite plusCommutative 1 ovc in ip) (Just edge)) Nothing]
buildStdTraversalArray' {vc = S vc'} (Node1 edge tree) (ip :: ips) = do
  let tail = buildStdTraversalArray' tree (rewrite plusSuccRightSucc ovc vc' in ips)
  (TTD ip (rewrite sym $ plusSuccRightSucc ovc vc' in convertEdge (rewrite plusSuccRightSucc ovc vc' in ip) edge) Nothing) :: (rewrite sym $ plusSuccRightSucc ovc vc' in tail)
buildStdTraversalArray' {vc = S vc'} (Node2 leftTree rightTree @{vcPrf}) (ip :: ips) = do
  let (leftIs, rightIs) = split vcPrf ips
  let leftArray : Vect ? (TreeTraversalData $ ovc + S vc') = rewrite leftSumRule1 vcPrf ovc in
        buildStdTraversalArray' leftTree (rewrite sym $ leftSumRule1 vcPrf ovc in leftIs)
  let rightArray : Vect ? (TreeTraversalData $ ovc + S vc') = rewrite rightSumRule1 vcPrf ovc in
        buildStdTraversalArray' rightTree (rewrite sym $ rightSumRule1 vcPrf ovc in rightIs)
  let (leftS ** leftI) = currentIndexPair $ head' leftArray
  let (rightS ** rightI) = currentIndexPair $ head' rightArray
  (TTD ip (Just $ weakenLTE leftI $ minusLTE (finToNat leftS) (ovc + S vc')) (Just $ weakenLTE rightI $ minusLTE (finToNat rightS) (ovc + S vc')))
    :: (rewrite cong (\x => Vect x $ TreeTraversalData (ovc + S vc')) $ sym $ natSumIsSum vcPrf in leftArray ++ rightArray)
    where
      head' : Vect k a -> GT k 0 => a  -- TODO: can I avoid it in a more convenient way?
      head' (x :: xs) @{(LTESucc _)} = x


public export
buildStdTraversalArray : {ovc : _} -> {vc : _} -> (tree : PrimaryTree ovc vc lc) -> Vect vc (TreeTraversalData (ovc + vc))
buildStdTraversalArray tree = buildStdTraversalArray' tree $ buildIndices tree 0

