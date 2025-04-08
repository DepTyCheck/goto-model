module Spec.Value.Value

import public Data.Fin
import public Spec.Misc

%default total

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
data VExpr : (vTy : VType) -> (isDet : Bool) -> (c : Nat) -> Type where
  Det : {vTy : _} -> (rawV : RawValue vTy) -> VExpr vTy True Z
  Undet : (vTy : _) -> (idx : Nat) -> VExpr vTy False Z
  Op : (vop : ValueOp) ->
       {vTyL, vTyR : _} -> {isDetL, isDetR : _} -> {cL, cR : _} ->
       VExpr vTyL isDetL cL -> VExpr vTyR isDetR cR ->
       IsOpVTypes vop vTyL vTyR vTy => BoolAnd isDetL isDetR isDet => NatSum cL cR c =>
       VExpr vTy isDet c

%name VExpr vExpr

public export
data Value : Type where
  Unkwn : Value
  JustV : {vTy : _} -> {isDet : _} -> {c : _} -> VExpr vTy isDet c -> Value

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
data HasType : (vTy : VType) -> (cLim : Nat) -> (vs : VectValue n) -> c `LTE` cLim => VExpr vTy isDet c -> Type where
  [search vTy vs]
  HasTypeHere : HasType vTy cLim (JustV {vTy} {c} vExpr :: vs') @{ltePrf} vExpr
  HasTypeThere : HasType vTy cLim vs' @{ltePrf} v -> HasType vTy cLim (v1 :: vs') @{ltePrf} v

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
data Produce : (vop : ValueOp) -> (cLim : Nat) -> (regs : VectValue n) -> Value -> Type where
  ProduceOp : HasType vTyL cLim regs {isDet=isDetL} {c=cL} @{ltePrfL} vExprL =>
              (ovtPrf : IsOpVTypes vop vTyL vTyR vTy) =>
              HasType vTyR (cLim `minus` cL) regs {isDet=isDetR} {c=cR} @{ltePrfR} vExprR =>
              Produce vop cLim regs (JustV $ Op vop vExprL vExprR @{ovtPrf} @{snd $ boolAnd isDetL isDetR} @{snd $ natSum01 cL cR})

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

