module Show.Tree

import public Text.PrettyPrint.Bernardy
import public Spec.Tree

prettyTree : PrimaryTree loc roc vc lc -> Doc opts
prettyTree x = ?prettyTree_rhs

Pretty (PrimaryTree loc roc vc lc) where
  prettyPrec _ = prettyTree

