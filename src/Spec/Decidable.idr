module Spec.Decidable


import public Control.Function
import public Decidable.Equality
import public Spec.Value


public export
Injective Spec.Value.Just where
  injective Refl = Refl

public export
Injective Spec.Value.RawI where
  injective Refl = Refl

public export
Injective Spec.Value.RawB where
  injective Refl = Refl

public export
{vTy : _} -> Injective (Spec.Value.Det {vTy}) where
  injective Refl = Refl

public export
{vTy : _} -> Injective (Spec.Value.Undet vTy) where
  injective Refl = Refl

public export
{mVTy : _} -> {isDet : _} -> Injective (V mVTy isDet) where
  injective Refl = Refl

public export
{v : _} -> Injective (Spec.Value.(::) v) where
  injective Refl = Refl


public export
DecEq (BoolAnd a b c) where
  decEq TrueAndTrue TrueAndTrue = Yes Refl
  decEq FalseAndAny FalseAndAny = Yes Refl
  decEq FalseAndAny AnyAndFalse = No $ \case Refl impossible
  decEq AnyAndFalse FalseAndAny = No $ \case Refl impossible
  decEq AnyAndFalse AnyAndFalse = Yes Refl

public export
DecEq VType where
  decEq B B = Yes Refl
  decEq B I = No $ \case Refl impossible
  decEq I I = Yes Refl
  decEq I B = No $ \case Refl impossible

public export
DecEq MaybeVType where
  decEq Nothing Nothing = Yes Refl
  decEq (Just a) (Just b) = decEqCong $ decEq a b
  decEq Nothing (Just b) = No $ \case Refl impossible
  decEq (Just a) Nothing = No $ \case Refl impossible

public export
DecEq ValueOp where
  decEq Add Add = Yes Refl
  decEq Add And = No $ \case Refl impossible
  decEq Add Or = No $ \case Refl impossible
  decEq And And = Yes Refl
  decEq And Add = No $ \case Refl impossible
  decEq And Or = No $ \case Refl impossible
  decEq Or Or = Yes Refl
  decEq Or Add = No $ \case Refl impossible
  decEq Or And = No $ \case Refl impossible

public export
DecEq (RawValue vTy) where
  decEq (RawI a) (RawI b) = decEqCong $ decEq a b
  decEq (RawB a) (RawB b) = decEqCong $ decEq a b

public export
DecEq (IsOpVTypes {}) where
  decEq ItIsAddVTypes ItIsAddVTypes = Yes Refl
  decEq ItIsAndVTypes ItIsAndVTypes = Yes Refl
  decEq ItIsOrVTypes ItIsOrVTypes = Yes Refl

%ambiguity_depth 5

public export
DecEq (VExpr {}) where
  decEq Unkwn Unkwn = Yes Refl
  decEq (Det rawV) (Det rawV') = decEqCong $ decEq rawV rawV'
  decEq (Undet vTy idx) (Undet vTy idx') = decEqCong $ decEq idx idx'
  decEq (Op {vTyL} {vTyR} {isDetL} {isDetR} vop vExprL vExprR @{ovtPrf} @{boolAnd})
        (Op {vTyL=vTyL'} {vTyR=vTyR'} {isDetL=isDetL'} {isDetR=isDetR'} vop' vExprL' vExprR' @{ovtPrf'} @{boolAnd'})
    with (decEq vop vop', decEq vTyL vTyL', decEq vTyR vTyR', decEq isDetL isDetL', decEq isDetR isDetR')
      decEq (Op {vTyL} {vTyR} {isDetL} {isDetR} vop vExprL vExprR)
            (Op {vTyL} {vTyR} {isDetL} {isDetR} vop vExprL' vExprR')
        | (Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl)
        with (decEq vExprL vExprL', decEq vExprR vExprR', decEq ovtPrf ovtPrf', decEq boolAnd boolAnd')
          decEq (Op {vTyL} {vTyR} {isDetL} {isDetR} vop vExprL vExprR @{ovtPrf} @{boolAnd})
                (Op {vTyL} {vTyR} {isDetL} {isDetR} vop vExprL vExprR @{ovtPrf} @{boolAnd})
            | (Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl) | (Yes Refl, Yes Refl, Yes Refl, Yes Refl) = Yes Refl
          decEq (Op {vTyL} {vTyR} {isDetL} {isDetR} vop vExprL vExprR @{ovtPrf} @{boolAnd})
                (Op {vTyL} {vTyR} {isDetL} {isDetR} vop vExprL vExprR @{ovtPrf} @{boolAnd'})
            | (Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl) | (Yes Refl, Yes Refl, Yes Refl, No contra) = No $ \case Refl => contra Refl
          decEq (Op {vTyL} {vTyR} {isDetL} {isDetR} vop vExprL vExprR @{ovtPrf} @{boolAnd})
                (Op {vTyL} {vTyR} {isDetL} {isDetR} vop vExprL vExprR @{ovtPrf'} @{boolAnd'})
            | (Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl) | (Yes Refl, Yes Refl, No contra, _) = No $ \case Refl => contra Refl
          decEq (Op {vTyL} {vTyR} {isDetL} {isDetR} vop vExprL vExprR @{ovtPrf} @{boolAnd})
                (Op {vTyL} {vTyR} {isDetL} {isDetR} vop vExprL vExprR' @{ovtPrf'} @{boolAnd'})
            | (Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl) | (Yes Refl, No contra, _, _) = No $ \case Refl => contra Refl
          decEq (Op {vTyL} {vTyR} {isDetL} {isDetR} vop vExprL vExprR @{ovtPrf} @{boolAnd})
                (Op {vTyL} {vTyR} {isDetL} {isDetR} vop vExprL' vExprR' @{ovtPrf'} @{boolAnd'})
            | (Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl) | (No contra, _, _, _) = No $ \case Refl => contra Refl
      decEq (Op {vTyL} {vTyR} {isDetL} {isDetR} vop vExprL vExprR)
            (Op {vTyL} {vTyR} {isDetL} {isDetR=isDetR'} vop vExprL' vExprR')
            | (Yes Refl, Yes Refl, Yes Refl, Yes Refl, No contra) = No $ \case Refl => contra Refl
      decEq (Op {vTyL} {vTyR} {isDetL} {isDetR} vop vExprL vExprR)
            (Op {vTyL} {vTyR} {isDetL=isDetL'} {isDetR=isDetR'} vop vExprL' vExprR')
            | (Yes Refl, Yes Refl, Yes Refl, No contra, _) = No $ \case Refl => contra Refl
      decEq (Op {vTyL} {vTyR} {isDetL} {isDetR} vop vExprL vExprR)
            (Op {vTyL} {vTyR=vTyR'} {isDetL=isDetL'} {isDetR=isDetR'} vop vExprL' vExprR')
            | (Yes Refl, Yes Refl, No contra, _, _) = No $ \case Refl => contra Refl
      decEq (Op {vTyL} {vTyR} {isDetL} {isDetR} vop vExprL vExprR)
            (Op {vTyL=vTyL'} {vTyR=vTyR'} {isDetL=isDetL'} {isDetR=isDetR'} vop vExprL' vExprR')
            | (Yes Refl, No contra, _, _, _) = No $ \case Refl => contra Refl
      decEq (Op {vTyL} {vTyR} {isDetL} {isDetR} vop vExprL vExprR)
            (Op {vTyL=vTyL'} {vTyR=vTyR'} {isDetL=isDetL'} {isDetR=isDetR'} vop' vExprL' vExprR')
            | (No contra, _, _, _, _) = No $ \case Refl => contra Refl
  decEq (Det {}) (Op {}) = No $ \case Refl impossible
  decEq (Undet {}) (Op {}) = No $ \case Refl impossible
  decEq (Op {}) (Det {}) = No $ \case Refl impossible
  decEq (Op {}) (Undet {}) = No $ \case Refl impossible

%ambiguity_depth 3

public export
DecEq Value where
  decEq (V mVTy isDet vExpr) (V mVTy' isDet' vExpr') with (decEq mVTy mVTy', decEq isDet isDet')
    decEq (V mVTy isDet vExpr) (V mVTy isDet vExpr') | (Yes Refl, Yes Refl) = decEqCong $ decEq vExpr vExpr'
    decEq (V mVTy isDet vExpr) (V mVTy isDet' vExpr') | (Yes Refl, No contra) = No $ \case Refl => contra Refl
    decEq (V mVTy isDet vExpr) (V mVTy' isDet' vExpr') | (No contra, _) = No $ \case Refl => contra Refl

public export
DecEq (VectValue {}) where
  decEq [] [] = Yes Refl
  decEq (v :: vs) (v' :: vs') = case decEq v v' of
                                     (Yes Refl) => decEqCong $ decEq vs vs'
                                     (No contra) => No $ \case Refl => contra Refl
