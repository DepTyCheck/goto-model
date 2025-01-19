module Show.Tree.Basic

import Data.Vect
import public Text.PrettyPrint.Bernardy
import Spec.Tree

Pretty (MaybeFin $ S n) where
  prettyPrec _ Nothing = ""
  prettyPrec _ (Just x) = pretty $ finToNat x


prettyTraversalArray : {opts : _} -> Vect k (TreeTraversalData (S n)) -> Doc opts
prettyTraversalArray [] = empty
prettyTraversalArray ((TTD i s e1 e2) :: xs) = do
  let hasE1 = e1 /= Nothing
  let hasE2 = e2 /= Nothing
  let hasAnyE = hasE1 || hasE2
  let nodeLine = Doc.line {opts} "\{show (finToNat i)}: "
                 <+> (if s == FZ then "leaf" else "node")
                 <+> when (e1 /= Nothing) (" " <+> pretty e1)
                 <+> when (e2 /= Nothing) (" " <+> pretty e2)
  vappend nodeLine $ prettyTraversalArray xs

public export
prettyTree : {opts : ?} -> {ovc : _} -> {vc : _} ->
             PrimaryTree ovc vc lc ->
             Doc opts
prettyTree {vc = S vc'} tree = prettyTraversalArray {opts} $ buildStdTraversalArray1 tree 0

