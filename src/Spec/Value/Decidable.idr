module Spec.Value.Decidable

import Spec.Value.Value
import Control.Function
import public Decidable.Equality

%default total

public export
Injective NatSumStep where
  injective Refl = Refl

public export
Injective Value.RawI where
  injective Refl = Refl

public export
Injective Value.RawB where
  injective Refl = Refl

public export
{vTy : _} -> Injective (Value.Det {vTy}) where
  injective Refl = Refl

public export
{vTy : _} -> Injective (Value.Undet vTy) where
  injective Refl = Refl

public export
{vTy : _} -> {isDet : _} -> {c : _} -> Injective (Value.JustV {vTy} {isDet} {c}) where
  injective Refl = Refl

public export
{v : _} -> Injective (Value.(::) v) where
  injective Refl = Refl

public export
DecEq (BoolAnd a b c) where
  decEq TrueAndTrue TrueAndTrue = Yes Refl
  decEq FalseAndAny FalseAndAny = Yes Refl
  decEq FalseAndAny AnyAndFalse = No $ \case Refl impossible
  decEq AnyAndFalse FalseAndAny = No $ \case Refl impossible
  decEq AnyAndFalse AnyAndFalse = Yes Refl

public export
DecEq (NatSum a b c) where
  decEq NatSumBase NatSumBase = Yes Refl
  decEq NatSumBase (NatSumStep p2') impossible
  decEq (NatSumStep _) NatSumBase impossible
  decEq (NatSumStep p1') (NatSumStep p2') = decEqCong $ decEq p1' p2'

public export
DecEq VType where
  decEq B B = Yes Refl
  decEq B I = No $ \case Refl impossible
  decEq I I = Yes Refl
  decEq I B = No $ \case Refl impossible

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
Eq (RawValue vTy) where
  (RawI x) == (RawI y) = x == y
  (RawB x) == (RawB y) = x == y

public export
DecEq (VExpr {}) where
  decEq (Det rawV) (Det rawV') = decEqCong $ decEq rawV rawV'
  decEq (Undet vTy idx) (Undet vTy idx') = decEqCong $ decEq idx idx'
  decEq (Op {vTyL} {vTyR} {isDetL} {isDetR} {cL} {cR} vop vExprL vExprR @{ovtPrf} @{boolAnd} @{natSum})
        (Op {vTyL=vTyL'} {vTyR=vTyR'} {isDetL=isDetL'} {isDetR=isDetR'} {cL=cL'} {cR=cR'} vop' vExprL' vExprR' @{ovtPrf'} @{boolAnd'} @{natSum'})
    with (decEq vop vop', decEq vTyL vTyL', decEq vTyR vTyR', decEq isDetL isDetL', decEq isDetR isDetR', decEq cL cL', decEq cR cR')
      decEq (Op {vTyL} {vTyR} {isDetL} {isDetR} {cL} {cR} vop vExprL vExprR @{ovtPrf} @{boolAnd} @{natSum})
            (Op {vTyL} {vTyR} {isDetL} {isDetR} {cL} {cR} vop vExprL' vExprR' @{ovtPrf'} @{boolAnd'} @{natSum'})
        | (Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl)
        with (decEq vExprL vExprL', decEq vExprR vExprR', decEq ovtPrf ovtPrf', decEq boolAnd boolAnd', decEq natSum natSum')
          decEq (Op {vTyL} {vTyR} {isDetL} {isDetR} {cL} {cR} vop vExprL vExprR @{ovtPrf} @{boolAnd} @{natSum})
                (Op {vTyL} {vTyR} {isDetL} {isDetR} {cL} {cR} vop vExprL vExprR @{ovtPrf} @{boolAnd} @{natSum})
            | (Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl) | (Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl) = Yes Refl
          decEq (Op {vTyL} {vTyR} {isDetL} {isDetR} {cL} {cR} vop vExprL vExprR @{ovtPrf} @{boolAnd} @{natSum})
                (Op {vTyL} {vTyR} {isDetL} {isDetR} {cL} {cR} vop vExprL vExprR @{ovtPrf} @{boolAnd} @{natSum'})
            | (Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl) | (Yes Refl, Yes Refl, Yes Refl, Yes Refl, No contra) = No $ \case Refl => contra Refl
          decEq (Op {vTyL} {vTyR} {isDetL} {isDetR} {cL} {cR} vop vExprL vExprR @{ovtPrf} @{boolAnd} @{natSum})
                (Op {vTyL} {vTyR} {isDetL} {isDetR} {cL} {cR} vop vExprL vExprR @{ovtPrf} @{boolAnd'} @{natSum'})
            | (Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl) | (Yes Refl, Yes Refl, Yes Refl, No contra, _) = No $ \case Refl => contra Refl
          decEq (Op {vTyL} {vTyR} {isDetL} {isDetR} {cL} {cR} vop vExprL vExprR @{ovtPrf} @{boolAnd} @{natSum})
                (Op {vTyL} {vTyR} {isDetL} {isDetR} {cL} {cR} vop vExprL vExprR @{ovtPrf'} @{boolAnd'} @{natSum'})
            | (Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl) | (Yes Refl, Yes Refl, No contra, _, _) = No $ \case Refl => contra Refl
          decEq (Op {vTyL} {vTyR} {isDetL} {isDetR} {cL} {cR} vop vExprL vExprR @{ovtPrf} @{boolAnd} @{natSum})
                (Op {vTyL} {vTyR} {isDetL} {isDetR} {cL} {cR} vop vExprL vExprR' @{ovtPrf'} @{boolAnd'} @{natSum'})
            | (Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl) | (Yes Refl, No contra, _, _, _) = No $ \case Refl => contra Refl
          decEq (Op {vTyL} {vTyR} {isDetL} {isDetR} {cL} {cR} vop vExprL vExprR @{ovtPrf} @{boolAnd} @{natSum})
                (Op {vTyL} {vTyR} {isDetL} {isDetR} {cL} {cR} vop vExprL' vExprR' @{ovtPrf'} @{boolAnd'} @{natSum'})
            | (Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl) | (No contra, _, _, _, _) = No $ \case Refl => contra Refl
      decEq (Op {vTyL} {vTyR} {isDetL} {isDetR} {cL} {cR} vop vExprL vExprR @{ovtPrf} @{boolAnd} @{natSum})
            (Op {vTyL} {vTyR} {isDetL} {isDetR} {cL} {cR=cR'} vop vExprL' vExprR' @{ovtPrf'} @{boolAnd'} @{natSum'})
        | (Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl, No contra) = No $ \case Refl => contra Refl
      decEq (Op {vTyL} {vTyR} {isDetL} {isDetR} {cL} {cR} vop vExprL vExprR @{ovtPrf} @{boolAnd} @{natSum})
            (Op {vTyL} {vTyR} {isDetL} {isDetR} {cL=cL'} {cR=cR'} vop vExprL' vExprR' @{ovtPrf'} @{boolAnd'} @{natSum'})
        | (Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl, No contra, _) = No $ \case Refl => contra Refl
      decEq (Op {vTyL} {vTyR} {isDetL} {isDetR} {cL} {cR} vop vExprL vExprR @{ovtPrf} @{boolAnd} @{natSum})
            (Op {vTyL} {vTyR} {isDetL} {isDetR=isDetR'} {cL=cL'} {cR=cR'} vop vExprL' vExprR' @{ovtPrf'} @{boolAnd'} @{natSum'})
        | (Yes Refl, Yes Refl, Yes Refl, Yes Refl, No contra, _, _) = No $ \case Refl => contra Refl
      decEq (Op {vTyL} {vTyR} {isDetL} {isDetR} {cL} {cR} vop vExprL vExprR @{ovtPrf} @{boolAnd} @{natSum})
            (Op {vTyL} {vTyR} {isDetL=isDetL'} {isDetR=isDetR'} {cL=cL'} {cR=cR'} vop vExprL' vExprR' @{ovtPrf'} @{boolAnd'} @{natSum'})
        | (Yes Refl, Yes Refl, Yes Refl, No contra, _, _, _) = No $ \case Refl => contra Refl
      decEq (Op {vTyL} {vTyR} {isDetL} {isDetR} {cL} {cR} vop vExprL vExprR @{ovtPrf} @{boolAnd} @{natSum})
            (Op {vTyL} {vTyR=vTyR'} {isDetL=isDetL'} {isDetR=isDetR'} {cL=cL'} {cR=cR'} vop vExprL' vExprR' @{ovtPrf'} @{boolAnd'} @{natSum'})
        | (Yes Refl, Yes Refl, No contra, _, _, _, _) = No $ \case Refl => contra Refl
      decEq (Op {vTyL} {vTyR} {isDetL} {isDetR} {cL} {cR} vop vExprL vExprR @{ovtPrf} @{boolAnd} @{natSum})
            (Op {vTyL=vTyL'} {vTyR=vTyR'} {isDetL=isDetL'} {isDetR=isDetR'} {cL=cL'} {cR=cR'} vop vExprL' vExprR' @{ovtPrf'} @{boolAnd'} @{natSum'})
        | (Yes Refl, No contra, _, _, _, _, _) = No $ \case Refl => contra Refl
      decEq (Op {vTyL} {vTyR} {isDetL} {isDetR} {cL} {cR} vop vExprL vExprR @{ovtPrf} @{boolAnd} @{natSum})
            (Op {vTyL=vTyL'} {vTyR=vTyR'} {isDetL=isDetL'} {isDetR=isDetR'} {cL=cL'} {cR=cR'} vop' vExprL' vExprR' @{ovtPrf'} @{boolAnd'} @{natSum'})
        | (No contra, _, _, _, _, _, _) = No $ \case Refl => contra Refl
  decEq (Det {}) (Op {}) = No $ \case Refl impossible
  decEq (Undet {}) (Op {}) = No $ \case Refl impossible
  decEq (Op {}) (Det {}) = No $ \case Refl impossible
  decEq (Op {}) (Undet {}) = No $ \case Refl impossible

%ambiguity_depth 3

public export
DecEq Value where
  decEq Unkwn Unkwn = Yes Refl
  decEq (JustV {vTy=vTy1} {isDet=isDet1} {c=c1} vExpr1) (JustV {vTy=vTy2} {isDet=isDet2} {c=c2} vExpr2) with (decEq vTy1 vTy2, decEq isDet1 isDet2, decEq c1 c2)
    decEq (JustV {vTy} {isDet} {c} vExpr1) (JustV {vTy} {isDet} {c} vExpr2) | (Yes Refl, Yes Refl, Yes Refl) = decEqCong $ decEq vExpr1 vExpr2
    decEq (JustV {vTy} {isDet} {c=c1} vExpr1) (JustV {vTy} {isDet} {c=c2} vExpr2) | (Yes Refl, Yes Refl, No contra) = No $ \case Refl => contra Refl
    decEq (JustV {vTy} {isDet=isDet1} {c=c1} vExpr1) (JustV {vTy} {isDet=isDet2} {c=c2} vExpr2) | (Yes Refl, No contra, _) = No $ \case Refl => contra Refl
    decEq (JustV {vTy=vTy1} {isDet=isDet1} {c=c1} vExpr1) (JustV {vTy=vTy2} {isDet=isDet2} {c=c2} vExpr2) | (No contra, _, _) = No $ \case Refl => contra Refl
  decEq Unkwn (JustV vExpr) = No $ \case Refl impossible
  decEq (JustV vExpr) Unkwn = No $ \case Refl impossible

public export
DecEq (VectValue {}) where
  decEq [] [] = Yes Refl
  decEq (v :: vs) (v' :: vs') = case decEq v v' of
                                     (Yes Refl) => decEqCong $ decEq vs vs'
                                     (No contra) => No $ \case Refl => contra Refl
