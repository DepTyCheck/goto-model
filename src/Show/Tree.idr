module Show.Tree

import Control.Monad.State
import Data.Vect
import public Text.PrettyPrint.Bernardy
import public Spec.Tree.Traversal

record PrettyTraversalState {opts : ?} (n : Nat) where
  constructor PTS

  savedDoc : Doc opts
  currentDoc : Doc opts
  positions : Vect n $ (Nat, Nat)
  backEdges : Vect n $ List $ Fin n

PrettyMonad : {opts : ?} -> (n : Nat) -> Type -> Type
PrettyMonad n = State $ PrettyTraversalState {opts} n

PrettyFun : {opts : ?} -> (verticesTotalCount : Nat) -> (verticesCount : Nat) -> Type
PrettyFun vtc vc = TreeTraversalData vtc -> PrettyMonad {opts} vc ()

PrettyTraversalFun : {opts : ?} -> (verticesTotalCount : Nat) -> (verticesCount : Nat) -> Type
PrettyTraversalFun vtc vc = (beforeF : PrettyFun vtc vc) -> (afterF : PrettyFun vtc vc) -> PrettyMonad {opts} vc ()


buildPrettyTraversalFun' : {opts : ?} -> Vect k (TreeTraversalData n) -> PrettyTraversalFun {opts} n n'
buildPrettyTraversalFun' [] beforeF afterF = pure ()
buildPrettyTraversalFun' (x :: xs) beforeF afterF = do
  (PTS ssdoc sdoc ps bEdges) <- get
  put $ (PTS empty empty ps bEdges)
  beforeF x
  buildPrettyTraversalFun' xs beforeF afterF
  (PTS _ cdoc ps bEdges) <- get
  put $ (PTS sdoc cdoc ps bEdges)
  afterF x
  modify $ \(PTS _ cdoc ps bEdges) => PTS ssdoc cdoc ps bEdges

buildPrettyTraversalFun : {opts : ?} -> {ovc : _} -> {vc : _} ->
                          (tree : PrimaryTree ovc vc lc) ->
                          PrettyTraversalFun {opts} (ovc + vc) vc
buildPrettyTraversalFun tree = buildPrettyTraversalFun' $ buildStdTraversalArray tree

Pretty (MaybeFin $ S n) where
  prettyPrec _ Nothing = ""
  prettyPrec _ (Just x) = pretty $ finToNat x

-- TODO: I want ASCII tree pretty printer
prettyTree : {opts : ?} -> {ovc : _} -> {vc : _} ->
             PrimaryTree ovc vc lc ->
             Doc opts
prettyTree tree with (anyTreeHasSize tree)
  prettyTree {vc = S vc'} tree | (LTESucc _) = do
  let treePrf = anyTreeHasSize tree
  let trF = buildPrettyTraversalFun {opts} tree
  currentDoc $ execState (PTS empty empty (replicate (S vc') (0, 0)) (replicate (S vc') []))
    $ trF (rewrite sym $ plusSuccRightSucc ovc vc' in prettyBeforeFun {opts1 = opts})
          (rewrite sym $ plusSuccRightSucc ovc vc' in prettyAfterFun {opts})
    where
      prettyBeforeFun : {opts1 : ?} -> PrettyFun {opts = opts1} (S $ ovc + vc') (S vc')
      prettyBeforeFun (TTD (s ** i) e1 e2) = do
        modify $ \(PTS sdoc cdoc ps bEdges) => do
          let hasE1 = e1 /= Nothing
          let hasE2 = e2 /= Nothing
          let hasAnyE = hasE1 || hasE2
          let nodeLine = Doc.line {opts = opts1} "\{show (finToNat i)}: "
                         <+> (if s == FZ then "leaf" else "node")
                         <+> when (e1 /= Nothing) (" " <+> pretty e1)
                         <+> when (e2 /= Nothing) (" " <+> pretty e2)
          PTS sdoc (vappend cdoc nodeLine) ps bEdges
      prettyAfterFun : {opts : ?} -> PrettyFun {opts} (S $ ovc + vc') (S vc')
      prettyAfterFun (TTD (s ** i) e1 e2) = do
        pure ()

{-
Pretty (PrimaryTree ovc vc lc) where
  prettyPrec _ = prettyTree
  -}
