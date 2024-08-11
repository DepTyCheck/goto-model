module Gens.Manual.TreeTraversal


import public Test.DepTyCheck.Gen
import Control.Monad.State
import Data.Fin
import public Spec.Tree

record TreeTraversalInnerData (n : Nat) where
  constructor TTID

  currentIndex : Fin n

genTreeTraversalHelper : Monad m => StrongTree vc lc -> StateT (TreeTraversalInnerData vc) (Gen NonEmpty) (TreeTraversal m)

export
genTreeTraversal : Monad m => StrongTree vc lc -> Gen NonEmpty $ TreeTraversal m
genTreeTraversal tree = (evalStateT (TTID FZ) $ genTreeTraversalHelper tree)

