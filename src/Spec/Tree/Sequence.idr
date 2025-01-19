module Spec.Tree.Sequence

import public Spec.Tree
import public Data.Vect

%default total


finPlusNat : {n : _} -> Fin n -> Nat -> Fin n
finPlusNat x 0 = x
finPlusNat x (S k) = finS $ finPlusNat x k

public export
record VertexData (n : Nat) where
  constructor GD

  index : Fin n
  leftEdge : MaybeFin n
  rightEdge : MaybeFin n

public export
VertexSequence : (n : Nat) -> (totalN : Nat) -> Type
VertexSequence n totalN = Vect n $ VertexData totalN

toAbstractGraph' : (atree : AbstractTree ps) ->
                   {m : _} ->
                   (currentIndex : Fin m) ->
                   VertexSequence (size atree) m
toAbstractGraph' Leaf currentIndex = [GD currentIndex Nothing Nothing]
toAbstractGraph' FakeLeaf currentIndex = [GD currentIndex (Just currentIndex) Nothing]  -- adding edge just to be able to find the FakeLeaf
toAbstractGraph' (Node1 atree') currentIndex = do
  let nextIndex = finS currentIndex
  (GD currentIndex (Just nextIndex) Nothing) :: toAbstractGraph' atree' nextIndex
toAbstractGraph' (Node2 leftAtree rightAtree) currentIndex = do
  let leftIndex = finS currentIndex
  let rightIndex = finPlusNat leftIndex (size leftAtree)
  (GD currentIndex Nothing Nothing) ::
  ((toAbstractGraph' leftAtree leftIndex) ++
   (toAbstractGraph' rightAtree rightIndex))

public export
toAbstractGraph : (atree : AbstractTree ps) ->
                  let n = size atree in
                  VertexSequence n n
toAbstractGraph atree = toAbstractGraph' atree (zero $ sizeIsSucc atree)
  where
    zero : IsSucc a -> Fin a
    zero ItIsSucc = FZ

