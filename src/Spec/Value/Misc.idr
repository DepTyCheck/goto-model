module Spec.Value.Misc

import public Spec.Value
import public Decidable.Decidable

%default total

public export
dependsOnlyOn : (idx : Nat) -> (vExpr : VExpr vTy isDet c) -> Bool
dependsOnlyOn _ (Det _) = True
dependsOnlyOn idx (Undet vTy idx') = idx == idx'
dependsOnlyOn idx (Op vop vExprL vExprR) = (dependsOnlyOn idx vExprL) && (dependsOnlyOn idx vExprR)

public export
hasVTy : VType -> Value -> Bool
hasVTy vTy Unkwn = False
hasVTy vTy (JustV {vTy = vTy'} vExpr) = isYes $ decEq vTy vTy'

public export
isDet : Value -> Bool
isDet Unkwn = False
isDet (JustV {isDet = isDet'} vExpr) = isDet'

public export
isUndet : Value -> Bool
isUndet = not . isDet

public export
hasUndet : VectValue n -> Bool
hasUndet [] = False
hasUndet (v :: vs) = isUndet v || hasUndet vs

public export
hasUndetAt : Fin n -> VectValue n -> Bool
hasUndetAt FZ (v :: vs) = isUndet v
hasUndetAt (FS i') (v :: vs) = hasUndetAt i' vs

public export
isUndetI : Value -> Bool
isUndetI v = isUndet v && hasVTy I v

public export
hasUndetI : VectValue n -> Bool
hasUndetI [] = False
hasUndetI (v :: vs) = isUndetI v || hasUndetI vs

