module Spec.Context

import public Spec.Value

%default total

namespace Source
  public export
  data Source : Nat -> Type where
    Src : VectValue n -> Source n

  %name Source src

  public export
  (.registers) : Source n -> VectValue n
  (.registers) (Src vs) = vs

  public export
  data MaybeSource : Nat -> Type where
    Nothing : MaybeSource n
    Just : Source n -> MaybeSource n

  public export
  data VectSource : Nat -> Nat -> Type where
    Nil : VectSource 0 n
    (::) : Source n -> VectSource m n -> VectSource (S m) n

  %name VectSource srcs

  public export
  foldr : (Source n -> acc -> acc) -> acc -> VectSource m n -> acc
  foldr f x [] = x
  foldr f x (src :: srcs) = f src (foldr f x srcs)

  public export
  data HasOneSource : MaybeSource n -> VectSource m n -> Type where
    HasImmSrc : HasOneSource (Just _) srcs
    HasOneSrc : HasOneSource msrc (src :: srcs)

namespace Bool
  public export
  data HasTrueBut : VectBool n -> MaybeSource m -> Type where
    HasTrueSure : HasTrue bs => HasTrueBut bs Nothing
    HasTrueMaybe : HasTrueBut bs (Just _)

namespace Source
  public export
  append' : MaybeSource n -> {l : _} -> VectSource l n -> (r ** VectSource r n)
  append' Nothing srcs = (_ ** srcs)
  append' (Just src) srcs = (_ ** src :: srcs)

  public export
  append'' : MaybeSource n -> {l : _} -> VectSource (S l) n -> (r ** VectSource (S r) n)
  append'' Nothing srcs = (_ ** srcs)
  append'' (Just src) srcs = (_ ** src :: srcs)

  public export
  extractAt : (idx : Fin $ S m) -> VectSource (S m) n -> (Source n, VectSource m n)
  extractAt _ (src :: []) = (src, [])
  extractAt FZ (src :: src1 :: srcs) = (src, src1 :: srcs)
  extractAt (FS idx') (src :: src1 :: srcs) = let (extracted, rem) = extractAt idx' (src1 :: srcs) in (extracted, src :: rem)

  public export
  extractAtMany' : (bs : VectBool m) -> VectSource m n -> ((k ** VectSource k n), (l ** VectSource l n))
  extractAtMany' [] [] = ((0 ** []), (0 ** []))
  extractAtMany' (b :: bs) (src :: srcs) = do
    let rec : ?; rec = extractAtMany' bs srcs
    -- TODO: (extracted, rem) = is broken, terrible syntax :(
    let extracted : ?; extracted = fst rec
    let rem : ?; rem = snd rec
    case b of
         True => ((_ ** src :: snd extracted), rem)
         False => (extracted, (_ ** src :: snd rem))

  public export
  extractAtMany : (bs : VectBool m) -> {msrc : MaybeSource n} -> HasTrueBut bs msrc => VectSource m n -> ((k' ** VectSource (S k') n), (l ** VectSource l n))
  extractAtMany [] {msrc = Nothing} @{HasTrueSure @{hasTrue}} [] = void $ lemma hasTrue
  where
    lemma : HasTrue [] -> Void
    lemma _ impossible
  -- TODO: cannot simply pattern match on hasTrue
  extractAtMany (b :: bs) {msrc = Nothing} @{HasTrueSure @{hasTrue}} (src :: srcs) with (hasTrue)
    extractAtMany (True :: bs) {msrc = Nothing} @{HasTrueSure @{hasTrue}} (src :: srcs) | Here = do
      let rec : ?; rec = extractAtMany' bs srcs
      let extracted : ?; extracted = fst rec
      let rem : ?; rem = snd rec
      ((_ ** src :: snd extracted), rem)
    extractAtMany (True :: bs) {msrc = Nothing} @{HasTrueSure @{hasTrue}} (src :: srcs) | (There hasTrue') = do
      let rec : ?; rec = extractAtMany bs @{HasTrueSure} srcs
      let extracted : ?; extracted = fst rec
      let rem : ?; rem = snd rec
      ((_ ** src :: snd extracted), rem)
    extractAtMany (False :: bs) {msrc = Nothing} @{HasTrueSure @{hasTrue}} (src :: srcs) | (There hasTrue') = do
      let rec : ?; rec = extractAtMany bs @{HasTrueSure} srcs
      let extracted : ?; extracted = fst rec
      let rem : ?; rem = snd rec
      (extracted, (_ ** src :: snd rem))
  extractAtMany bs {msrc = Just src} @{HasTrueMaybe} srcs = do
    let rec : ?; rec = extractAtMany' bs srcs
    let extracted : ?; extracted = fst rec
    let rem : ?; rem = snd rec
    ((_ ** src :: snd extracted), rem)

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
      mergeValues uc (JustV {vTy} {isDet} vExpr1) (JustV {vTy} {isDet} vExpr2) | (Yes Refl, Yes Refl) =
        case decEq vExpr1 vExpr2 of
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

