module Spec.Misc

import public Data.Fin

%default total

namespace Bool
  public export
  data OnlyOne : Bool -> Bool -> Type where
    OnlyFirst : OnlyOne True False
    OnlySecond : OnlyOne False True

  public export
  data NotAll : Bool -> Bool -> Type where
    NotFirst : NotAll False _
    NotSecond : NotAll _ False

  public export
  data BoolAnd : (a : Bool) -> (b : Bool) -> Bool -> Type where
    [search a b]
    TrueAndTrue : BoolAnd True True True
    FalseAndAny : BoolAnd False _ False
    AnyAndFalse : BoolAnd _ False False

  public export
  boolAnd : (a : Bool) -> (b : Bool) -> (c ** BoolAnd a b c)
  boolAnd False b = (False ** FalseAndAny)
  boolAnd True False = (False ** AnyAndFalse)
  boolAnd True True = (True ** TrueAndTrue)

  public export
  data VectBool : Nat -> Type where
    Nil : VectBool 0
    (::) : Bool -> VectBool n -> VectBool (S n)

  public export
  length : VectBool n -> Nat
  length [] = 0
  length (_ :: vs) = S $ length vs

  public export
  lengthIsCorrect : (vs : VectBool n) -> n = length vs
  lengthIsCorrect [] = Refl
  lengthIsCorrect (_ :: vs) = cong S $ lengthIsCorrect vs

  public export
  data HasTrue : VectBool n -> Type where
    Here : HasTrue (True :: bs)
    There : HasTrue bs -> HasTrue (b :: bs)

  public export
  Uninhabited (HasTrue []) where
    uninhabited _ impossible

  public export
  hasTrueIsSucc : {bs : VectBool n} -> HasTrue bs -> IsSucc n
  hasTrueIsSucc {bs = True :: _} Here = ItIsSucc
  hasTrueIsSucc {bs = _ :: _} (There _) = ItIsSucc

namespace Nat
  public export
  data NatSum : Nat -> Nat -> Nat -> Type where
    NatSumBase : NatSum a Z a
    NatSumStep : NatSum a b c -> NatSum a (S b) (S c)

  public export
  natSum01 : (a : Nat) -> (b : Nat) -> (c ** NatSum a b c)
  natSum01 a 0 = (a ** NatSumBase)
  natSum01 a (S b') = do
    let rec : ?; rec = natSum01 a b'
    (_ ** NatSumStep $ snd rec)

  public export
  data NotSame : Nat -> Nat -> Type where
    NotSameLeftBase : NotSame Z (S m')
    NotSameRightBase : NotSame (S n') Z
    NotSameStep : NotSame n m -> NotSame (S n) (S m)

namespace Fin
  public export
  data NotSame : Fin n -> Fin n -> Type where
    NotSameLeftBase : NotSame FZ (FS j)
    NotSameRightBase : NotSame (FS i) FZ
    NotSameStep : NotSame i j -> NotSame (FS i) (FS j)

