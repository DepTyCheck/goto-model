module Spec.Tree

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

{-
1) There is a source through which any vertex is reachable
2) There is a leaf (vertex without any out-edges)
3) Any vertex can have no more than 2 out-edges

Vertex is Leaf iff it has 0 edges
Vertex is Node iff it has > 0 edges
Node is open iff it has < 2 edges

outer count - number of mythical vertices outside of the tree that are guaranteed to be linkable

The standard enumeration:
1) Starts from the root, which has the index 0
2) Left child first, right child second

Edge is not an index from this numeration. Instead, it is de Brujin index, which
must be interpolated as an index in the enumeration sequence.
First vc values are for the subtree, the remaining ovc values are for the outer vertices
-}
public export
data PrimaryTree : (outerVerticesCount : Nat) -> (verticesCount : Nat) -> (leafsCount : Nat) -> Type where
  Leaf : PrimaryTree ovc 1 1
  FakeLeaf : (edge : Fin $ ovc + 1) -> PrimaryTree ovc 1 0  -- ovc + 1 to match the final type of FakeLeaf, it's useful when building traversalArray

  Node1 : (edge : MaybeFin (ovc + S vc)) ->  -- S vc to match the final type of Node1
          PrimaryTree (S ovc) vc lc ->  -- continuation
          PrimaryTree ovc (S vc) lc
  
  -- TODO: lc can be changed to bool
  Node2 : {leftVc : _} -> {rightVc : _} -> {vc : _} ->
          (leftTree : PrimaryTree (S $ ovc + rightVc) leftVc leftLc) ->
          (rightTree : PrimaryTree (S $ ovc + leftVc) rightVc rightLc) ->
          NatSum leftVc rightVc vc =>
          NatSum leftLc rightLc lc =>
          PrimaryTree ovc (S vc) lc

%name PrimaryTree tree


%hint
public export
anyTreeHasSize : PrimaryTree ovc vc lc -> LT 0 vc
anyTreeHasSize Leaf = LTESucc LTEZero
anyTreeHasSize (FakeLeaf x) = LTESucc LTEZero
anyTreeHasSize (Node1 edge tree) = LTESucc LTEZero
anyTreeHasSize (Node2 tree tree1) = LTESucc LTEZero

public export
size : PrimaryTree ovc vc lc -> Nat
size Leaf = 1
size (FakeLeaf x) = 1
size (Node1 edge tree) = S (size tree)
size (Node2 leftTree rightTree) = S (size leftTree + size rightTree)

%hint
public export
sizeCorrect : (tree : PrimaryTree ovc vc lc) -> size tree = vc
sizeCorrect Leaf = Refl
sizeCorrect (FakeLeaf edge) = Refl
sizeCorrect (Node1 edge tree) = cong S $ sizeCorrect tree
sizeCorrect (Node2 leftTree rightTree @{vcPrf}) = let leftPrf = sizeCorrect leftTree
                                                      rightPrf = sizeCorrect rightTree in cong S $ rewrite sym $ natSumIsSum vcPrf in
                                                                                                   rewrite leftPrf in
                                                                                                   rewrite rightPrf in Refl

public export
size' : {vc : _} -> PrimaryTree ovc vc lc -> Nat
size' tree = vc

public export
finLT : (a : Fin n) -> LT (finToNat a) n
finLT FZ = LTESucc LTEZero
finLT (FS x) = LTESucc (finLT x)

public export
StrongTree : (vc : Nat) -> (lc : Nat) -> Type
StrongTree vc lc = PrimaryTree 0 vc lc

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
test3 = Node1 Nothing $ Node1 (Just 1) $ Leaf  -- because Node1 increments ovc, so 1 refers to the vertex 0 from the picture

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

 0
/ \
1 3<|
| | |
2 4 |
  | |
  5-|

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
test5 = Node2 (Node1 (Just 2){-ovc=1+3,vc=1-} $ Leaf) (Node1 (Just 2){-ovc=1+2,vc=2-} $ Node1 Nothing $ FakeLeaf 0{-ovc=5,vc=0-})

{-

|<|
0 |
|-|
-}
test6 : StrongTree 1 0
test6 = FakeLeaf 0
