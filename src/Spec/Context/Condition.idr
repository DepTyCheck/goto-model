module Spec.Context.Condition

import public Spec.Value.Value

public export
data PrimaryPredicate : (vTy : VType) -> Type where
  LessThan : PrimaryPredicate I
  Equal : PrimaryPredicate I
  LessThanOrEqual : PrimaryPredicate I
  IsTrue : PrimaryPredicate B

%name PrimaryPredicate pp

public export
data PredicateConstant : PrimaryPredicate vTy -> Type where
  NoConstant : PredicateConstant IsTrue
  Constant : {0 pp : PrimaryPredicate I} -> Nat -> PredicateConstant pp

%name PredicateConstant c

-- Condition data
public export
data ConData : VectValue n -> Type where
  CD : (regIdx : Fin n) ->
       (pp : PrimaryPredicate vTy) ->
       (c : PredicateConstant pp) ->
       (neg : Bool) ->
       ConData {n} vs

%name ConData cd

namespace Maybe
  public export
  data MaybeConData : VectValue n -> Type where
    Nothing : MaybeConData vs
    Just : ConData vs -> MaybeConData vs

  %name MaybeConData mcd

