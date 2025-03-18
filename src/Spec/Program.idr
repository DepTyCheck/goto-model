module Spec.Program

import public Spec.Value.Decidable


%default total


namespace Bool
  public export
  data VectBool : Nat -> Type where
    Nil : VectBool 0
    (::) : Bool -> VectBool n -> VectBool (S n)

  public export
  data HasTrue : VectBool n -> Type where
    Here : HasTrue (True :: bs)
    There : HasTrue bs -> HasTrue (b :: bs)


namespace Source
  public export
  data Source : Nat -> Type where
    Src : VectValue n -> Source n

  %name Source src

  public export
  (.registers) : Source n -> VectValue n
  (.registers) (Src vs) = vs

  public export
  data VectSource : Nat -> Nat -> Type where
    Nil : VectSource 0 n
    (::) : Source n -> VectSource m n -> VectSource (S m) n

  %name VectSource srcs

  public export
  extractAt : (idx : Fin $ S m) -> VectSource (S m) n -> (Source n, VectSource m n)
  extractAt _ (src :: []) = (src, [])
  extractAt FZ (src :: src1 :: srcs) = (src, src1 :: srcs)
  extractAt (FS idx') (src :: src1 :: srcs) = let (extracted, rem) = extractAt idx' (src1 :: srcs) in (extracted, src :: rem)

  public export
  extractAtMany' : (bs : VectBool m) -> VectSource m n -> ((k ** VectSource k n), (l ** VectSource l n))
  extractAtMany' [] [] = ((0 ** []), (0 ** []))
  extractAtMany' (b :: bs) (src :: srcs) = do
    let (extracted, rem) = extractAtMany' bs srcs
    case b of
         True => ((_ ** src :: snd extracted), rem)
         False => (extracted, (_ ** src :: snd rem))

  public export
  extractAtMany : (bs : VectBool m) -> HasTrue bs => VectSource m n -> ((k' ** VectSource (S k') n), (l ** VectSource l n))
  extractAtMany [] [] impossible
  extractAtMany (False :: bs) @{There hasTrue'} (src :: srcs) = let (extracted, rem) = extractAtMany bs srcs in (extracted, (_ ** src :: snd rem))
  extractAtMany (True :: bs) @{hasTrue} (src :: srcs) = let (extracted, rem) = extractAtMany' bs srcs in ((_ ** src :: snd extracted), rem)

  public export
  mergeStep : Nat -> VectSource (S k') (S n) -> (Nat, Value, VectSource (S k') n)
  mergeStep uc ((Src $ Unkwn :: vs) :: []) = (uc, Unkwn, [Src vs])
  mergeStep uc ((Src $ (JustV {vTy} {isDet = False} vExpr) :: vs) :: []) = (S uc, JustV $ Undet vTy uc, [Src vs])
  mergeStep uc ((Src $ v@(JustV {isDet = True} vExpr) :: vs) :: []) = (uc, v, [Src vs])
  mergeStep uc ((Src $ v :: vs) :: src1 :: srcs) = do
    let (_, merged, rest) = mergeStep 0 (src1 :: srcs)
    let (uc1, v1) = mergeValues uc v merged
    (uc1, v1, Src vs :: rest)
  where
    mergeValues : Nat -> Value -> Value -> (Nat, Value)
    mergeValues uc Unkwn v2 = (uc, Unkwn)
    mergeValues uc (JustV vExpr) Unkwn = (uc, Unkwn)
    mergeValues uc (JustV {vTy=vTy1} {isDet=isDet1} vExpr1) (JustV {vTy=vTy2} {isDet=isDet2} vExpr2) with (decEq vTy1 vTy2, decEq isDet1 isDet2)
      mergeValues uc (JustV {vTy} {isDet} vExpr1) (JustV {vTy} {isDet} vExpr2) | (Yes Refl, Yes Refl) = case decEq vExpr1 vExpr2 of
                                                                                                             (Yes Refl) => if isDet
                                                                                                                              then (uc, JustV vExpr1)
                                                                                                                              else (S uc, JustV $ Undet vTy uc)
                                                                                                             (No _) => (S uc, JustV $ Undet vTy uc)
      mergeValues uc (JustV {vTy} {isDet=isDet1} vExpr1) (JustV {vTy} {isDet=isDet2} vExpr2) | (Yes Refl, No _) = (S uc, JustV $ Undet vTy uc)
      mergeValues uc (JustV {vTy=vTy1} {isDet=isDet1} vExpr1) (JustV {vTy=vTy2} {isDet=isDet2} vExpr2) | (No _, _) = (uc, Unkwn)

  public export
  merge' : {n : _} -> Nat -> VectSource (S k') n -> (Nat, Source n)
  merge' {n=Z} _ _ = (0, Src [])
  merge' {n=S n'} uc (src :: srcs) = do
    let (uc1, mergedZero, rest) = mergeStep uc (src :: srcs)
    let (uc2, Src regs') = merge' uc1 rest
    (uc2, Src $ mergedZero :: regs')

  public export
  merge : {n : _} -> VectSource (S k') n -> Source n 
  merge = snd . (merge' 0)


namespace LinearBlock
  public export
  data LinearBlock : VectValue n -> VectValue n -> Type where
    Assign : (target, i : Fin n) ->
             LinearBlock (duplicate target i regs) finalRegs ->
             LinearBlock regs finalRegs
    RegOp : (target : Fin n) ->
            Produce vop regs v =>
            LinearBlock (replaceAt target v regs) finalRegs ->
            LinearBlock regs finalRegs
    Finish : LinearBlock regs regs


namespace Possible
  public export
  data IsUndet : Fin n -> VectValue n -> Type where
    Here : IsUndet 0 (JustV {vTy} {isDet=False} _ :: vs)
    There : IsUndet idx' vs -> IsUndet (FS idx') (v :: vs)
  
  public export
  data Possible : VectSource l n -> VectValue n -> VectSource r n -> Type where
    ItIsPossibleToExit : Possible srcs regs srcs
    ItIsPossibleToJmp : Possible srcs regs $ Src regs :: srcs
    ItIsPossibleToCondjmp : IsUndet i regs => Possible srcs regs (Src regs :: Src regs :: srcs)


public export
data Program : (srcs : VectSource n m) -> Type where
  -- l m n srcs finalRegs contSrcs bs HasTrue LinearBlock  Possible  Program
  -- 0 1 2   3        4        5   6       7          8        9       10
  Step : {n : _} -> {srcs : VectSource m n} -> {finalRegs : VectValue n} -> {contSrcs : VectSource l n} ->
         (bs : VectBool m) ->
         HasTrue bs =>
         let extr : ((k' ** VectSource (S k') n), (l ** VectSource l n)); extr = extractAtMany bs srcs in
         let merged : Source n; merged = merge $ snd $ fst extr in
         LinearBlock merged.registers finalRegs ->
         Possible (snd $ snd extr) finalRegs contSrcs =>
         Program contSrcs ->
         Program srcs
  Finish : Program []

