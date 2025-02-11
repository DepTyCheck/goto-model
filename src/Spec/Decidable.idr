module Spec.Decidable


import public Decidable.Equality
import public Spec.Value


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
  decEq (Just a) (Just b) = case decEq a b of
                                 (Yes Refl) => Yes Refl
                                 (No contra) => No $ \case Refl => contra Refl
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
DecEq (RawValue I) where
  decEq (RawI a) (RawI b) = case decEq a b of
                                 (Yes Refl) => Yes Refl
                                 (No contra) => No $ \case Refl => contra Refl

public export
DecEq (RawValue B) where
  decEq (RawB a) (RawB b) = case decEq a b of
                                 (Yes Refl) => Yes Refl
                                 (No contra) => No $ \case Refl => contra Refl

public export
DecEq (VExpr Nothing False) where
  decEq Unkwn Unkwn = Yes Refl

%ambiguity_depth 5

public export
DecEq (VExpr (Just I) isDet) where
  decEq (Det rawV1) (Det rawV2) = case decEq rawV1 rawV2 of
                                       (Yes Refl) => Yes Refl
                                       (No contra) => No $ \case Refl => contra Refl
  decEq (Det rawV) (Op vop vExpr vExpr1) = No $ \case Refl impossible
  decEq (Undet I idx1) (Undet I idx2) = case decEq idx1 idx2 of
                                             (Yes Refl) => Yes Refl
                                             (No contra) => No $ \case Refl => contra Refl
  decEq (Undet I _) (Op vop vExpr vExpr1) = No $ \case Refl impossible
  decEq (Op vop vExpr vExpr1) (Det rawV) = No $ \case Refl impossible
  decEq (Op vop vExpr vExpr1) (Undet I _) = No $ \case Refl impossible
  decEq (Op vop {vTyL} {vTyR} {isDetL} {isDetR} vExprL vExprR @{ovtPrf} @{boolAnd})
        (Op vop' {vTyL=vTyL'} {vTyR=vTyR'} {isDetL=isDetL'} {isDetR=isDetR'} vExprL' vExprR' @{ovtPrf'} @{boolAnd'}) with (decEq vop vop', decEq vTyL vTyL', decEq vTyR vTyR', decEq isDetL isDetL', decEq isDetR isDetR', ovtPrf, ovtPrf')
    decEq (Op Add {vTyL=I} {vTyR=I} {isDetL} {isDetR} vExprL vExprR @{ItIsAddVTypes} @{boolAnd})
          (Op Add {vTyL=I} {vTyR=I} {isDetL} {isDetR} vExprL' vExprR' @{ItIsAddVTypes} @{boolAnd'}) | (Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl, ItIsAddVTypes, ItIsAddVTypes) with (decEq vExprL vExprL', decEq vExprR vExprR', decEq boolAnd boolAnd')
      decEq (Op Add {vTyL=I} {vTyR=I} {isDetL} {isDetR} vExprL vExprR @{ItIsAddVTypes} @{boolAnd})
            (Op Add {vTyL=I} {vTyR=I} {isDetL} {isDetR} vExprL vExprR @{ItIsAddVTypes} @{boolAnd}) | (Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl, ItIsAddVTypes, ItIsAddVTypes) | (Yes Refl, Yes Refl, Yes Refl) = Yes Refl
      decEq (Op Add {vTyL=I} {vTyR=I} {isDetL} {isDetR} vExprL vExprR @{ItIsAddVTypes} @{boolAnd})
            (Op Add {vTyL=I} {vTyR=I} {isDetL} {isDetR} vExprL vExprR @{ItIsAddVTypes} @{boolAnd'}) | (Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl, ItIsAddVTypes, ItIsAddVTypes) | (Yes Refl, Yes Refl, No contra) = No $ \case Refl => contra Refl
      decEq (Op Add {vTyL=I} {vTyR=I} {isDetL} {isDetR} vExprL vExprR @{ItIsAddVTypes} @{boolAnd})
            (Op Add {vTyL=I} {vTyR=I} {isDetL} {isDetR} vExprL vExprR' @{ItIsAddVTypes} @{boolAnd'}) | (Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl, ItIsAddVTypes, ItIsAddVTypes) | (Yes Refl, No contra, _) = No $ \case Refl => contra Refl
      decEq (Op Add {vTyL=I} {vTyR=I} {isDetL} {isDetR} vExprL vExprR @{ItIsAddVTypes} @{boolAnd})
            (Op Add {vTyL=I} {vTyR=I} {isDetL} {isDetR} vExprL' vExprR' @{ItIsAddVTypes} @{boolAnd'}) | (Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl, ItIsAddVTypes, ItIsAddVTypes) | (No contra, _, _) = No $ \case Refl => contra Refl
    -- TODO: it's just a copy of the case above
    decEq (Op vop {vTyL} {vTyR} {isDetL} {isDetR} vExprL vExprR @{ovtPrf} @{boolAnd})
      (Op vop {vTyL} {vTyR} {isDetL} {isDetR} vExprL' vExprR' @{ovtPrf'} @{boolAnd'}) | (Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl, _, _) = do
      case ovtPrf of
           ItIsAddVTypes => do
             case ovtPrf' of
                  ItIsAddVTypes => do
                    case decEq vExprL vExprL' of
                         (Yes Refl) => do
                           case decEq vExprR vExprR' of
                                (Yes Refl) => do
                                  case decEq boolAnd boolAnd' of
                                       (Yes Refl) => Yes Refl
                                       (No contra) => No $ \case Refl => contra Refl
                                (No contra) => No $ \case Refl => contra Refl
                         (No contra) => No $ \case Refl => contra Refl
    decEq (Op vop {vTyL} {vTyR} {isDetL} {isDetR} vExprL vExprR @{ovtPrf} @{boolAnd})
          (Op vop {vTyL} {vTyR} {isDetL} {isDetR=isDetR'} vExprL' vExprR' @{ovtPrf'} @{boolAnd'}) | (Yes Refl, Yes Refl, Yes Refl, Yes Refl, No contra, _, _) = No $ \case Refl => contra Refl
    decEq (Op vop {vTyL} {vTyR} {isDetL} {isDetR} vExprL vExprR @{ovtPrf} @{boolAnd})
          (Op vop {vTyL} {vTyR} {isDetL=isDetL'} {isDetR=isDetR'} vExprL' vExprR' @{ovtPrf'} @{boolAnd'}) | (Yes Refl, Yes Refl, Yes Refl, No contra, _, _, _) = No $ \case Refl => contra Refl
    decEq (Op vop {vTyL} {vTyR} {isDetL} {isDetR} vExprL vExprR @{ovtPrf} @{boolAnd})
          (Op vop {vTyL} {vTyR=vTyR'} {isDetL=isDetL'} {isDetR=isDetR'} vExprL' vExprR' @{ovtPrf'} @{boolAnd'}) | (Yes Refl, Yes Refl, No contra, _, _, _, _) = No $ \case Refl => contra Refl
    decEq (Op vop {vTyL} {vTyR} {isDetL} {isDetR} vExprL vExprR @{ovtPrf} @{boolAnd})
          (Op vop {vTyL=vTyL'} {vTyR=vTyR'} {isDetL=isDetL'} {isDetR=isDetR'} vExprL' vExprR' @{ovtPrf'} @{boolAnd'}) | (Yes Refl, No contra, _, _, _, _, _) = No $ \case Refl => contra Refl
    decEq (Op vop {vTyL} {vTyR} {isDetL} {isDetR} vExprL vExprR @{ovtPrf} @{boolAnd})
          (Op vop' {vTyL=vTyL'} {vTyR=vTyR'} {isDetL=isDetL'} {isDetR=isDetR'} vExprL' vExprR' @{ovtPrf'} @{boolAnd'}) | (No contra, _, _, _, _, _, _) = No $ \case Refl => contra Refl

%ambiguity_depth 3
