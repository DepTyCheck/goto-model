module Spec.Program

import Data.Fin
import Data.Vect


{-
Out of a node can be 2 edges

How do I want to express this thing?

          0
         / \
        1   2
         \ /
          3
          
          0
         / \
        /   \
       /    2
      /    / \
     1    3---4

jmp is senseless?
Let's take any CFG and treeify it (select a tree with the root in 0 vertex, reaching every other vertice).
From now, any additional edge that CFG must have will start in a vertex with at least one out-edge! Thus,
these vertices represent a block with condjmp in their ends.

Where is jmp then?
Jmp is omitted, but it's inside of the tree structure. Any of the tree's edge can be easily considered
as a jmp moment.

Corollary:
I can think of condjmps only
-}

namespace BSListNat  -- bounded sorted list of Nats
  data BSListNat : (bound : Nat) -> Type
  data IsBS : (bound : Nat) -> Nat -> BSListNat bound -> Type

  public export
  data BSListNat : (bound : Nat) -> Type where
    Nil : BSListNat bound
    (::) : (x : Nat) -> (xs : BSListNat bound) -> IsBS bound x xs => BSListNat bound

  public export
  data IsBS : (bound : Nat) -> Nat -> (l : BSListNat bound) -> Type where
    IsBSBase : LT x bound -> IsBS bound x []
    IsBSStep : LT x y -> IsBS bound y ys -> IsBS bound x (y :: ys)

  %name IsBS bsPrf

  data Contains : Nat -> BSListNat bound -> Type where
    ContainsHit : Contains x ((::) x ys @{prf})
    ContainsMiss : Contains x xs -> Contains x ((::) y xs @{prf})

  %name Contains containsPrf

  isBsImpliesLt : {bound : _} -> {x : _} -> {xs : _} -> IsBS bound x xs -> LT x bound
  isBsImpliesLt (IsBSBase y) = y
  isBsImpliesLt (IsBSStep ltPrf bsPrf) = transitive ltPrf $ lteSuccLeft $ isBsImpliesLt bsPrf

  containsImpliesFin : {bound : _} -> {l : BSListNat bound} -> Contains x l -> LT x bound
  containsImpliesFin {l = ((::) x ys @{bsPrf})} ContainsHit = isBsImpliesLt bsPrf
  containsImpliesFin {l = (y :: xs)} (ContainsMiss containsPrf) = containsImpliesFin containsPrf


public export
data NatSum : (a : Nat) -> Nat -> Nat -> Type where
  [search a]
  NatSumBase : NatSum 0 b b
  NatSumStep : NatSum a b c -> NatSum (S a) b (S c)

public export
MaybeFin : Nat -> Type
MaybeFin = Maybe . Fin

public export
data PrimaryTree : (nodeCount : Nat) -> (verticesCount : Nat) -> Type where
  Leaf : PrimaryTree 0 1
  FakeLeaf : PrimaryTree 1 1

  Node1 : MaybeFin vc ->  -- edge from a new node
          BSListNat nc ->  -- edges to the root from the continuation
          PrimaryTree nc vc ->  -- continuation
          PrimaryTree (S nc) (S vc)

  Node2 : Vect k (MaybeFin $ S u) ->  -- edges from the left continuation
          Vect m (MaybeFin $ S t) ->  -- edges from the right continuation
          PrimaryTree k t ->
          PrimaryTree m u ->
          NatSum k m nc =>
          NatSum t u vc =>
          PrimaryTree (S nc) (S vc)

public export
StrongTree : (nc : Nat) -> (vc : Nat) -> LT nc vc => Type
StrongTree nc vc = PrimaryTree nc vc

{-

0

-}
test1 : StrongTree 0 1
test1 = Leaf

{-

0
|
1

-}
test2 : StrongTree 1 2
test2 = Node1 Nothing [] $ Leaf

{-

0<|
| |
1-|
|
2

-}
test3 : StrongTree 2 3
test3 = Node1 Nothing [0] $ Node1 Nothing [] $ Leaf

{-

0-|
| |
1 |
| |
2<|

-}
test4 : StrongTree 2 3
test4 = Node1 (Just 1) [] $ Node1 Nothing [] $ Leaf

{-

0----|
|    |
1--->3<|
|   /| |
2<-/ | |
     4 |
     | |
     5-|

-}
test5 : StrongTree 5 6
test5 = Node2 [Just 1] [Just 2, Nothing, Nothing] (Node1 Nothing [] $ Leaf) (Node1 Nothing [1] $ Node1 Nothing [] $ FakeLeaf)
