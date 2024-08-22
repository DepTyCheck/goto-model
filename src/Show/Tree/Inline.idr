module Show.Tree.Inline


import Data.Fin
import public Text.PrettyPrint.Bernardy
import public Spec.Tree


Pretty (Fin (S n)) where
  prettyPrec _ = line . show

Pretty (MaybeFin (S n)) where
  prettyPrec _ Nothing = "Nothing"
  prettyPrec p (Just x) = prettyPrec p x

public export
prettyTree : {opts : _} -> PrimaryTree ovc vc lc -> Doc opts
prettyTree Leaf = "Leaf"
prettyTree (FakeLeaf edge) = let edge' : Fin (S ovc) = rewrite sym $ plusCommutative ovc 1 in edge
  in "FakeLeaf" <++> pretty edge'
prettyTree {vc = S vc'} (Node1 edge tree) = let edge' : MaybeFin (S ovc + vc') = rewrite plusSuccRightSucc ovc vc' in edge
  in "Node1" <++> pretty edge' <++> (parens $ prettyTree {opts} tree)
prettyTree (Node2 leftTree rightTree) = "Node2" <++> (parens $ prettyTree {opts} leftTree) <++> (parens $ prettyTree {opts} rightTree)

