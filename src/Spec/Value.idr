module Spec.Value

import public Data.Fin
import public Spec.Misc


public export
data VType = I | B

%name VType vTy

public export
data MaybeVType = Nothing | Just VType

%name MaybeVType mVTy

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
data VExpr : MaybeVType -> Bool -> Type where
  Unkwn : VExpr Nothing False
  Det : {vTy : _} -> (rawV : RawValue vTy) -> VExpr (Just vTy) True
  Undet : (vTy : _) -> (idx : Nat) -> VExpr (Just vTy) False
  Op : (vop : ValueOp) ->
       {vTyL, vTyR : _} -> {isDetL, isDetR : _} ->
       VExpr (Just vTyL) isDetL -> VExpr (Just vTyR) isDetR ->
       IsOpVTypes vop vTyL vTyR vTy => BoolAnd isDetL isDetR isDet =>
       VExpr (Just vTy) isDet

%name VExpr vExpr

public export
record Value where
  constructor V

  mtype : MaybeVType
  isDetermined : Bool
  raw : VExpr mtype isDetermined

%name Value v

public export
data Produce : (vop : ValueOp) -> (lv : Value) -> (rv : Value) -> Value -> Type where
  [search vop lv rv]
  -- TODO: ProduceDet
  ProduceOp : IsOpVTypes vop vTyL vTyR vTy =>
              BoolAnd isDetL isDetR isDet =>
              Produce vop (V (Just vTyL) isDetL vExprL) (V (Just vTyR) isDetR vExprR) $ V (Just vTy) isDet (Op vop vExprL vExprR)

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

