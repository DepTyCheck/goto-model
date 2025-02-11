module Spec.Misc


%default total


namespace Logic
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

namespace Nat
  public export
  data NatSum : Nat -> Nat -> Nat -> Type where
    NatSumBase : NatSum a Z a
    NatSumStep : NatSum a b c => NatSum a (S b) (S c)

  public export
  data NotSame : Nat -> Nat -> Type where
    NotSameLeftBase : NotSame Z (S m')
    NotSameRightBase : NotSame (S n') Z
    NotSameStep : NotSame n m => NotSame (S n) (S m)
