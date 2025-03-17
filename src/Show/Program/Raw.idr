module Show.Program.Raw

import Spec.Program

import Data.String

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
Show (Source n) where
  show (Src uc vs) = "(\{show uc}, \{show vs})"

public export
Show (ListSource n) where
  show ss = "[\{show' ss}]"
    where
      show' : ListSource m -> String
      show' [] = ""
      show' [s] = show s
      show' (s1 :: s2 :: ss'') = "\{show s1}, " <+> show' (s2 :: ss'')

public export
toIndex : HasType vTy vs vExpr -> Nat
toIndex HasTypeHere = Z
toIndex (HasTypeThere hasTy') = S $ toIndex hasTy'

public export
Show (Program {n=S n'} ctx) where
  show (Assign target i cont) = unlines ["Assign \{show target} <- \{show i}", show cont]
  show (RegOp vop target @{ProduceOp @{hasTyL} @{_} @{hasTyR}} cont) = do
    let li = toIndex hasTyL
    let ri = toIndex hasTyR
    unlines ["\{show vop} \{show target} <- \{show li} \{show ri}", show cont]
  show (Sink {ctx = Ctx _ _ _ _ fs} @{ItIsSankInWithLoop _} {contFs} cont) =
    unlines ["fs before sink: \{show fs}", "fs after sink into loop: \{show contFs}", show cont]
  show (Sink {ctx = Ctx _ _ _ _ fs} @{_} {contFs} cont) =
    unlines ["fs before sink: \{show fs}", "fs after sink: \{show contFs}", show cont]
  show (Source0 cont) = unlines ["Source0", show cont]
  show (Source1 @{_} @{Backward} cont) = unlines ["Source1, backward", show cont]
  show (Source1 @{_} @{Forward _} cont) = unlines ["Source1, forward", show cont]
  show (Source2 cont) = unlines ["Source2", show cont]
  show Finish = ""
