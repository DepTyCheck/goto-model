module Spec.Tree

import public Data.Fin
import Data.Vect


namespace VectMaybeFin
  public export
  data MaybeFin : Nat -> Type where
    Nothing : MaybeFin n
    Just : Fin n -> MaybeFin n

  %name MaybeFin x

  public export
  applyRule : MaybeFin n -> (n = m) -> MaybeFin m
  applyRule x Refl = x

  public export
  weaken : MaybeFin n -> MaybeFin (S n)
  weaken Nothing = Nothing
  weaken (Just x) = Just $ weaken x

  public export
  Eq (MaybeFin $ S n) where
    (==) Nothing Nothing = True
    (==) (Just x) (Just y) = True
    (==) _ _ = False

  public export
  data VectMaybeFin : (len : Nat) -> (bound : Nat) -> Type where
    Nil : VectMaybeFin 0 bound
    (::) : MaybeFin bound -> VectMaybeFin n bound -> VectMaybeFin (S n) bound

  %name VectMaybeFin xs


public export
data NatSum : (a : Nat) -> Nat -> Nat -> Type where
--  [search a]
  NatSumBase : NatSum 0 b b
  NatSumStep : NatSum a b c -> NatSum (S a) b (S c)

%name NatSum sumPrf

public export
natSumIsSum : NatSum a b c -> a + b = c
natSumIsSum NatSumBase = Refl
natSumIsSum (NatSumStep sumPrf) = cong S $ natSumIsSum sumPrf

public export
getNatSumSecond : (a : Nat) -> (c : Nat) -> LTE a c => (b ** NatSum a b c)
getNatSumSecond 0 c @{LTEZero} = (c ** NatSumBase)
getNatSumSecond (S a') (S c') @{(LTESucc ltePrf')} = let (b ** recPrf) = getNatSumSecond a' c' in (b ** NatSumStep recPrf)

public export
record Params where
  constructor Prms

  -- verticesCount = node1Count + node2Count + leavesCount + fakeLeavesCount
  node1Count : Nat
  node2Count : Nat
  leavesCount : Nat
  fakeLeavesCount : Nat

public export
data SumParams : Params -> Params -> Params -> Type where
  MkSumParams : NatSum leftN1c rightN1c n1c =>
                NatSum leftN2c rightN2c n2c =>
                NatSum leftLc rightLc lc =>
                NatSum leftFlc rightFlc flc =>
                SumParams (Prms leftN1c leftN2c leftLc leftFlc) (Prms rightN1c rightN2c rightLc rightFlc) (Prms n1c n2c lc flc)

public export
data AbstractTree : Params -> Type where
  Leaf : AbstractTree (Prms 0 0 1 0)
  FakeLeaf : AbstractTree (Prms 0 0 0 1)
  Node1 : AbstractTree (Prms n1c n2c lc flc) -> AbstractTree (Prms (S n1c) n2c lc flc)
  Node2 : AbstractTree leftPs ->
          AbstractTree rightPs ->
          SumParams leftPs rightPs (Prms n1c n2c lc flc) =>
          AbstractTree (Prms n1c (S n2c) lc flc)

%name AbstractTree atree

public export
(.params) : {ps : _} -> AbstractTree ps -> Params
(.params) {ps} _ = ps

public export
size : AbstractTree ps -> Nat
size Leaf = 1
size FakeLeaf = 1
size (Node1 atree) = S (size atree)
size (Node2 leftAtree rightAtree) = S (size leftAtree + size rightAtree)

%hint
public export
sizeIsSucc : (atree : AbstractTree ps) -> IsSucc (size atree)
sizeIsSucc Leaf = ItIsSucc
sizeIsSucc FakeLeaf = ItIsSucc
sizeIsSucc (Node1 atree) = ItIsSucc
sizeIsSucc (Node2 atree atree1) = ItIsSucc

plusEq : left = right -> left' = right' -> left `plus` left' = right `plus` right'
plusEq Refl Refl = Refl

plusRedistribution : {0 a, b, a', b' : Nat} -> (a + a') + (b + b') = (a + b) + (a' + b')
plusRedistribution = rewrite sym $ plusAssociative a a' (b + b') in
                             rewrite plusAssociative a' b b' in
                                     rewrite plusCommutative a' b in
                                             rewrite sym $ plusAssociative b a' b' in
                                                     rewrite plusAssociative a b (a' + b') in Refl

public export
sizeIsVerticesCount : (atree : AbstractTree (Prms n1c n2c lc flc)) -> (size atree) = (n1c + n2c + lc + flc)
sizeIsVerticesCount Leaf = Refl
sizeIsVerticesCount FakeLeaf = Refl
sizeIsVerticesCount (Node1 atree) = cong S (sizeIsVerticesCount atree)
sizeIsVerticesCount {n2c = S n2c'} (Node2 leftAtree rightAtree @{MkSumParams @{n1cPrf} @{n2cPrf} @{lcPrf} @{flcPrf}}) =
  rewrite sym $ plusSuccRightSucc n1c n2c' in do
    let leftRec = sizeIsVerticesCount leftAtree
    let rightRec = sizeIsVerticesCount rightAtree
    let plusRec = plusEq leftRec rightRec
    cong S $ rewrite sym $ natSumIsSum n1cPrf in rewrite sym $ natSumIsSum n2cPrf in
                     rewrite sym $ natSumIsSum lcPrf in rewrite sym $ natSumIsSum flcPrf in rewriteLemma plusRec
  where
    rewriteLemma : {s1, s2, a, b, c, d, a', b', c', d' : Nat} ->
                   s1 + s2 = (a + b + c + d) + (a' + b' + c' + d') -> s1 + s2 = (a + a') + (b + b') + (c + c') + (d + d')
    rewriteLemma {a, b, c, d, a', b', c', d'} prf = rewrite plusRedistribution {a = a, b = b, a' = a', b' = b'} in
                                                            rewrite plusRedistribution {a = a + b, b = c, a' = a' + b', b' = c'} in
                                                                    rewrite plusRedistribution {a = a + b + c, b = d, a' = a' + b' + c', b' = d'} in prf

