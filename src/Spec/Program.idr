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
namespace VectMaybeFin
  public export
  data MaybeFin : Nat -> Type where
    Nothing : MaybeFin n
    Just : Fin n -> MaybeFin n

  public export
  data VectMaybeFin : (len : Nat) -> (bound : Nat) -> Type where
    Nil : VectMaybeFin 0 bound
    (::) : MaybeFin bound -> VectMaybeFin n bound -> VectMaybeFin (S n) bound


public export
data NatSum : (a : Nat) -> Nat -> Nat -> Type where
--  [search a]
  NatSumBase : NatSum 0 b b
  NatSumStep : NatSum a b c -> NatSum (S a) b (S c)


{-
1) There is a source through which any vertex is reachable
2) There is a leaf (vertex without any out-edges)
3) Any vertex can have no more than 2 out-edges

Vertex is Leaf iff it has 0 edges
Vertex is Node iff it has > 0 edges
Node is open iff it has < 2 edges

outer count - number of mythical vertices outside of the tree that are guaranteed to be linkable
-}


public export
data PrimaryTree : (leftOutersCount : Nat) -> (rightOutersCount : Nat) -> (verticeCount : Nat) -> (leafsCount : Nat) -> Type where
  Leaf : PrimaryTree loc roc 1 1
  FakeLeaf : Fin (loc + roc) -> PrimaryTree loc roc 1 0

  Node1 : (edge : MaybeFin (loc + vc + roc)) ->
          PrimaryTree loc (S roc) vc lc ->  -- continuation
          PrimaryTree loc roc (S vc) lc
  
  Node2 : PrimaryTree loc (S (roc + rightVc)) leftVc leftLc ->
          PrimaryTree (S (loc + leftVc)) roc rightVc rightLc ->
          NatSum leftVc rightVc vc =>
          NatSum leftLc rightLc lc =>
          PrimaryTree loc roc (S vc) lc

public export
StrongTree : (vc : Nat) -> (lc : Nat) -> Type
StrongTree vc lc = PrimaryTree 0 0 vc lc

{-

0

-}
test1 : StrongTree 1 1
test1 = Leaf

{-

0
|
1

-}
test2 : StrongTree 2 1
test2 = Node1 Nothing $ Leaf

{-

0<|
| |
1-|
|
2

-}
test3 : StrongTree 3 1
test3 = Node1 Nothing $ Node1 (Just 1) $ Leaf  -- because Node1 increments roc, so 1 refers to the vertex 0 from the picture

{-

0-|
| |
1 |
| |
2<|

-}
test4 : StrongTree 3 1
test4 = Node1 (Just 1) $ Node1 Nothing $ Leaf  -- now 1 is just a part from vc, so it refers to the vertex 2

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
test5' : StrongTree 3 0
test5' = Node1 Nothing $ Node1 Nothing $ FakeLeaf 0

test5 : StrongTree 6 1
test5 = Node2 (Node1 (Just 2){-loc=0,vc=1,roc=1+3-} $ Leaf) (Node1 (Just 2){-loc=1+2,vc=2,roc=0-} $ Node1 Nothing $ FakeLeaf 0{-loc=1+2,vc=0,roc=2-})
