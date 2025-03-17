module Spec.Value

import public Data.Fin
import public Spec.Misc


public export
data VType = I | B

%name VType vTy

public export
data ValueOp = Add | And | Or

%name ValueOp vop

public export
data IsOpVTypes : (vop : ValueOp) -> (vTyL : VType) -> (vTyR : VType) -> VType -> Type where
  [search vop vTyL vTyR]
  ItIsAddVTypes : IsOpVTypes Add I I I
  ItIsAndVTypes : IsOpVTypes And B B B
  ItIsOrVTypes : IsOpVTypes Or B B B

%name IsOpVTypes ovtPrf

public export
data RawValue : VType -> Type where
  RawI : Nat -> RawValue I
  RawB : Bool -> RawValue B

%name RawValue rawV

public export
data VExpr : VType -> Bool -> Type where
  Det : {vTy : _} -> (rawV : RawValue vTy) -> VExpr vTy True
  Undet : (vTy : _) -> (idx : Nat) -> VExpr vTy False
  Op : (vop : ValueOp) ->
       {vTyL, vTyR : _} -> {isDetL, isDetR : _} ->
       VExpr vTyL isDetL -> VExpr vTyR isDetR ->
       IsOpVTypes vop vTyL vTyR vTy => BoolAnd isDetL isDetR isDet =>
       VExpr vTy isDet

%name VExpr vExpr

public export
data Value : Type where
  Unkwn : Value
  JustV : {vTy : _} -> {isDet : _} -> VExpr vTy isDet -> Value

%name Value v

public export
data VectValue : Nat -> Type where
  Nil : VectValue 0
  (::) : Value -> VectValue n -> VectValue (S n)

%name VectValue vs

public export
data Index : (i : Fin n) -> (vs : VectValue n) -> Value -> Type where
  [search i vs]
  IndexBase : Index FZ (v :: vs) v
  IndexStep : Index i' vs v -> Index (FS i') (v' :: vs) v

public export
data HasType : (vTy : VType) -> (vs : VectValue n) -> VExpr vTy isDet -> Type where
  [search vTy vs]
  HasTypeHere : HasType vTy (JustV {vTy} vExpr :: vs') vExpr
  HasTypeThere : HasType vTy vs' v -> HasType vTy (v1 :: vs') v

public export
data ReplaceAt : (i : Fin n) -> (v : Value) -> (vs : VectValue n) -> VectValue n -> Type where
  [search i v vs]
  ReplaceHere : ReplaceAt FZ v (v' :: vs') (v :: vs')
  ReplaceThere : ReplaceAt i' v vs' newVs' => ReplaceAt (FS i') v (v1 :: vs') (v1 :: newVs')

public export
data Duplicate : (dst : Fin n) -> (src : Fin n) -> (vs : VectValue n) -> VectValue n -> Type where
  [search dst src vs]
  JustDup : Index src vs v => ReplaceAt dst v vs newVs => Duplicate dst src vs newVs

public export
data Produce : ValueOp -> VectValue n -> Value -> Type where
  ProduceOp : HasType vTyL regs {isDet=isDetL} vExprL =>
              (ovtPrf : IsOpVTypes vop vTyL vTyR vTy) =>
              HasType vTyR regs {isDet=isDetR} vExprR =>
              Produce vop regs (JustV $ Op vop vExprL vExprR @{ovtPrf} @{snd $ boolAnd isDetL isDetR})

public export
index : Fin n -> VectValue n -> Value
index FZ (v :: vs) = v
index (FS i') (v :: vs) = index i' vs

public export
replaceAt : Fin n -> Value -> VectValue n -> VectValue n
replaceAt FZ v (v1 :: vs) = v :: vs
replaceAt (FS i') v (v1 :: vs) = v1 :: replaceAt i' v vs

public export
duplicate : (dst : Fin n) -> (src : Fin n) -> VectValue n -> VectValue n
duplicate dst src vs = replaceAt dst (index src vs) vs

