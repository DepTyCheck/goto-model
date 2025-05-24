module Spec.Context.Source

import public Spec.Value
import public Spec.Context.Condition
import public Control.Monad.State

public export
data Source : Nat -> Type where
  Src : (regs : VectValue n) -> MaybeConData regs -> Source n

%name Source src

public export
(.registers) : Source n -> VectValue n
(.registers) (Src vs mcd) = vs

namespace Maybe
  public export
  data MaybeSource : Nat -> Type where
    Nothing : MaybeSource n
    Just : Source n -> MaybeSource n

namespace Vect
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

public export
append' : MaybeSource n -> {l : _} -> VectSource l n -> (r ** VectSource r n)
append' Nothing srcs = (_ ** srcs)
append' (Just src) srcs = (_ ** src :: srcs)

public export
extractAtMany' : (bs : VectBool m) -> VectSource m n -> ((k ** VectSource k n), (l ** VectSource l n))
extractAtMany' [] [] = ((0 ** []), (0 ** []))
extractAtMany' (b :: bs) (src :: srcs) = do
  let rec : ?; rec = extractAtMany' bs srcs
  let extracted : ?; extracted = fst rec
  let rem : ?; rem = snd rec
  case b of
       True => ((_ ** src :: snd extracted), rem)
       False => (extracted, (_ ** src :: snd rem))

public export
extractAtMany : (bs : VectBool m) -> HasTrue bs => VectSource m n -> ((k' ** VectSource (S k') n), (l ** VectSource l n))
extractAtMany (True :: bs) @{Here} (src :: srcs) = do
  let rec : ?; rec = extractAtMany' bs srcs
  let extracted : ?; extracted = fst rec
  let rem : ?; rem = snd rec
  ((_ ** src :: snd extracted), rem)
extractAtMany (b :: bs) @{There _} (src :: srcs) = do
  let rec : ?; rec = extractAtMany bs srcs
  let extracted : ?; extracted = fst rec
  let rem : ?; rem = snd rec
  case b of
       True => ((_ ** src :: snd extracted), rem)
       False => (extracted, (_ ** src :: snd rem))

public export
erase : VType -> StateT Bool (State Nat) Value
erase vTy = do
  uc <- lift get
  put True
  lift $ put (S uc)
  pure $ JustV $ Undet vTy uc

public export
eraseOrSkip : VType -> Value -> StateT Bool (State Nat) Value
eraseOrSkip vTy v = do
  isErased <- get
  if isErased
     then pure v
     else erase vTy

public export
mergeValues : Value -> Value -> Nat -> StateT {-isErased-}Bool (State Nat) Value
mergeValues Unkwn v2 uc = do
  lift $ put uc  -- reset uc in state back no matter what is v2
  pure Unkwn
mergeValues (JustV vExpr) Unkwn uc = pure Unkwn  -- uc is already reset
mergeValues (JustV {vTy=vTy1} {isDet=isDet1} {c=c1} vExpr1) (JustV {vTy=vTy2} {isDet=isDet2} {c=c2} vExpr2) uc with (decEq vTy1 vTy2, decEq isDet1 isDet2, decEq c1 c2)
  mergeValues (JustV {vTy} {isDet} {c} vExpr1) (JustV {vTy} {isDet} {c} vExpr2) uc | (Yes Refl, Yes Refl, Yes Refl) =
    case decEq vExpr1 vExpr2 of
         (Yes Refl) => pure $ JustV vExpr1
         (No _) => do
           if isDet
              then erase vTy  -- if isErased then isDet == False
              else eraseOrSkip vTy (JustV vExpr2)
  mergeValues (JustV {vTy} {isDet} {c=c1} vExpr1) (JustV {vTy} {isDet} {c=c2} vExpr2) uc | (Yes Refl, Yes Refl, No _) = eraseOrSkip vTy (JustV vExpr2)
  mergeValues (JustV {vTy} {isDet=isDet1} {c=c1} vExpr1) (JustV {vTy} {isDet=isDet2} {c=c2} vExpr2) uc | (Yes Refl, No _, _) = eraseOrSkip vTy (JustV vExpr2)
  mergeValues (JustV {vTy=vTy1} {isDet=isDet1} {c=c1} vExpr1) (JustV {vTy=vTy2} {isDet=isDet2} {c=c2} vExpr2) uc | (No _, _, _) = do
    lift $ put uc  -- reset uc in state
    pure Unkwn


public export
mergeStep' : IsSucc k => VectSource k (S n) -> StateT Bool (State Nat) (Value, VectSource k n)
mergeStep' @{ItIsSucc} [Src (v :: vs) _] = pure (v, [Src vs Nothing])
mergeStep' @{ItIsSucc} ((Src (v :: vs) _) :: src :: srcs) = do
  uc <- lift get
  (merged', rest) <- mergeStep' (src :: srcs)
  merged <- mergeValues v merged' uc
  pure (merged, Src vs Nothing :: rest)

public export
mergeStep : IsSucc k => VectSource k (S n) -> State Nat (Value, VectSource k n)
mergeStep = (evalStateT False) . mergeStep'

public export
merge' : {n : _} -> IsSucc k => VectSource k n -> State Nat $ Source n
merge' {n = 0} srcs = pure $ Src [] Nothing
merge' {n = S n'} @{ItIsSucc} (src :: srcs) = do
  (mergedZero, rest) <- mergeStep (src :: srcs)
  Src mergedRest _ <- merge' rest
  pure $ Src (mergedZero :: mergedRest) Nothing

public export
merge : {n : _} -> IsSucc k => VectSource k n -> (uc : Nat) -> (Source n, Nat)
merge srcs uc = swap $ runState uc $ merge' srcs

