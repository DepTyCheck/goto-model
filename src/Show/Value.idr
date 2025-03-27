module Show.Value

import Spec.Value.Value

public export
Show VType where
  show I = "I"
  show B = "B"

public export
Show ValueOp where
  show Add = "Add"
  show And = "And"
  show Or = "Or"

public export
Show (VExpr mVTy isDet) where
  show (Det (RawI i)) = "D(I \{show i})"
  show (Det (RawB b)) = "D(B \{show b})"
  show (Undet vTy idx) = "U(\{show vTy}, \{show idx})"
  show (Op vop vExprL vExprR) = "(\{show vExprL} \{show vop} \{show vExprR})"

public export
Show Value where
  show Unkwn = "Unkwn"
  show (JustV vExpr) = show vExpr

public export
Show (VectValue n) where
  show vs = "[\{show' vs}]"
    where
      show' : VectValue m -> String
      show' [] = ""
      show' [v] = show v
      show' (v1 :: v2 :: vs'') = "\{show v1}, " <+> show' (v2 :: vs'')

public export
toIndex : HasType vTy vs vExpr -> Nat
toIndex HasTypeHere = Z
toIndex (HasTypeThere hasTy') = S $ toIndex hasTy'

