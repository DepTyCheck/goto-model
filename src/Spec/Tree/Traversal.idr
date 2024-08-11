module Spec.Tree.Traversal

import Control.Monad.State
import Data.Fin
import Data.Vect
import Spec.Tree


public export
record TreeTraversalData (n : Nat) where
  constructor TTD

  currentIndex : Fin n
  leftEdge : MaybeFin n
  rightEdge : MaybeFin n

public export
TreeTraversalFun : (n : Nat) -> (Type -> Type) -> Type
TreeTraversalFun n m = ((TreeTraversalData n -> m ()) -> m ())

record InnerTreeTraversalData (n : Nat) where
  constructor ITTD

  currentIndex : Fin n


buildStdTraversalArray' : (tree : PrimaryTree loc roc vc lc) ->
                          let n = size tree in State () (Vect n (TreeTraversalData n))

buildStdTraversalArray : (tree : PrimaryTree loc roc vc lc) ->
                         let n = size tree in Vect n (TreeTraversalData n)
buildStdTraversalArray tree = ?buildStdTraversalArray_rhs

public export
buildStdTraversalFun : (tree : PrimaryTree loc roc vc lc) -> {m : Type -> Type} -> TreeTraversalFun (size tree) m

