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
  show (Det (RawI i)) = "I \{show i}"
  show (Det (RawB b)) = "B \{show b}"
  show (Undet vTy idx) = "Undet(\{show vTy}, \{show idx})"
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
  show (Sink {ctx = Ctx [] uc regs isInLB fs} {contCtx = Ctx _ _ _ _ contFs} cont) = do
    unlines ["fs before sink: \{show fs}", "fs after sink: \{show contFs}", show cont]
  show (Sink {ctx = Ctx ((L savedCtx initRegs gs ls) :: ols') uc regs isInLB fs} {contCtx = Ctx _ _ _ _ contFs} cont) = do
    unlines ["fs after sink in loop: \{show contFs}", show cont]
  show (Source0 cont) = unlines ["Source0", show cont]
  show (Source1 cont) = unlines ["Source1", show cont]
  show (Source2 cont) = unlines ["Source2", show cont]
  show Finish = ""
