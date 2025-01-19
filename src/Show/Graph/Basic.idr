module Show.Graph.Basic

import public Text.PrettyPrint.Bernardy
import Spec.Graph

Pretty (MaybeFin $ S n) where
  prettyPrec _ Nothing = ""
  prettyPrec _ (Just x) = pretty $ finToNat x

prettyGraph' : {opts : ?} -> Vect n (GraphData (S m)) -> Doc opts
prettyGraph' [] = empty
prettyGraph' ((GD i e1 e2) :: xs) = do
  let hasE1 = e1 /= Nothing
  let hasE2 = e2 /= Nothing
  let hasAnyE = hasE1 || hasE2
  let nodeLine = Doc.line {opts} "\{show (finToNat i)}: "
                 <+> (if not hasAnyE then "leaf" else "node")
                 <+> when hasE1 (" " <+> pretty e1)
                 <+> when hasE2 (" " <+> pretty e2)
  vappend nodeLine $ prettyGraph' xs

public export
prettyGraph : {opts : ?} -> {n' : _} -> let n = S n' in
              Vect n (GraphData n) -> Doc opts
prettyGraph = prettyGraph'

