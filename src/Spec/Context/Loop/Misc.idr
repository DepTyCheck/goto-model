module Spec.Context.Loop.Misc

import public Spec.Context.Loop
import public Spec.Context.Decidable
import public Decidable.Decidable

%default total

namespace Guarantee
  public export
  count : Guarantee -> VectGuarantee n -> Nat
  count g [] = Z
  count g (g1 :: gs) = do
    let rec : ?; rec = count g gs
    if isYes $ decEq g g1
       then S rec
       else rec

  public export
  has : Guarantee -> VectGuarantee n -> Bool
  has g gs = count g gs > Z

public export
head : ListLoop n -> MaybeLoop n
head [] = Nothing
head (l :: _) = Just l

public export
tail : ListLoop n -> ListLoop n
tail [] = []
tail (_ :: ls) = ls

public export
dependsOnlyOn : (idx : Nat) -> (vExpr : VExpr vTy isDet c) -> Bool
dependsOnlyOn _ (Det _) = True
dependsOnlyOn idx (Undet vTy idx') = idx == idx'
dependsOnlyOn idx (Op vop vExprL vExprR) = (dependsOnlyOn idx vExprL) && (dependsOnlyOn idx vExprR)

public export
hasUndet : VectValue n -> Bool
hasUndet [] = False
hasUndet (Unkwn :: vs) = hasUndet vs
hasUndet ((JustV {isDet = False} vExpr) :: vs) = True
hasUndet ((JustV {isDet = True} vExpr) :: vs) = hasUndet vs

public export
hasUndetDependsOnlyOnSelf' : (initRegs : VectValue n) -> AreWinded' savedRegs gs initRegs uc initUc
                          => (finalRegs : VectValue n) -> CanUnwindAll initRegs gs finalRegs => Bool
hasUndetDependsOnlyOnSelf' [] @{AreWindedBase'} [] @{CanUnwindAllBase} = False
hasUndetDependsOnlyOnSelf' ((JustV $ Undet vTy uc) :: initRegs) @{AreWindedStep' @{IsWindedGValue' @{IsWindedUndet'}} areWinded''}
                          ((JustV $ Undet vTy uc) :: finalRegs) @{CanUnwindAllStep @{CanUnwindGValue} _} = True
hasUndetDependsOnlyOnSelf' ((JustV vExpr) :: initRegs) @{AreWindedStep' @{IsWindedGValue' @{IsWindedDet'}} areWinded''}
                          ((JustV vExpr) :: finalRegs) @{CanUnwindAllStep @{CanUnwindGValue} _} =
  hasUndetDependsOnlyOnSelf' initRegs @{areWinded''} finalRegs
hasUndetDependsOnlyOnSelf' ((JustV $ Undet vTy initIdx) :: initRegs) @{AreWindedStep' @{IsWindedGType'} areWinded''}
                          ((JustV {isDet = finalIsDet} finalExpr) :: finalRegs) @{CanUnwindAllStep @{CanUnwindGType} _} = do
  let b : Bool; b = case finalIsDet of
                         True => False
                         False => dependsOnlyOn initIdx finalExpr
  b || hasUndetDependsOnlyOnSelf' initRegs @{areWinded''} finalRegs
hasUndetDependsOnlyOnSelf' (Unkwn :: initRegs) @{AreWindedStep' @{IsWindedGNothing'} areWinded''}
                          (fr :: finalRegs) @{CanUnwindAllStep @{CanUnwindGNothing} _} =
  hasUndetDependsOnlyOnSelf' initRegs @{areWinded''} finalRegs
hasUndetDependsOnlyOnSelf' _ _ = trace ("Unreachable!!!!!!") False  -- TODO: compiler is broken :(

public export
hasUndetDependsOnlyOnSelf : (initRegs : VectValue n) -> AreWinded savedRegs gs initRegs initUc
                         => (finalRegs : VectValue n) -> CanUnwindAll initRegs gs finalRegs => Bool
hasUndetDependsOnlyOnSelf initRegs @{TheyAreWinded @{areWinded'}} finalRegs @{canUnwindAll} =
  hasUndetDependsOnlyOnSelf' initRegs @{areWinded'} finalRegs @{canUnwindAll}

public export
areGuaranteesWeaklyPreserved : (gs : VectGuarantee n) -> (initRegs : VectValue n) -> (finalRegs : VectValue m) -> Bool
areGuaranteesWeaklyPreserved [] [] finalRegs = True
areGuaranteesWeaklyPreserved (GValue :: gs) (ir :: initRegs) finalRegs =
  (contains ir finalRegs) && areGuaranteesWeaklyPreserved gs initRegs finalRegs
  where
    contains : forall n . Value -> VectValue n -> Bool
    contains v [] = False
    contains v (v1 :: vs) = case decEq v v1 of
                                 (Yes _) => True
                                 (No _) => contains v vs
areGuaranteesWeaklyPreserved (_ :: gs) (ir :: initRegs) finalRegs =
  areGuaranteesWeaklyPreserved gs initRegs finalRegs

public export
unwindValue : {vTy : _} -> {isDet, finalIsDet : _} -> {c, finalC : _}
           -> (savedExpr : VExpr vTy isDet c) -> (initIdx : Nat) -> (finalExpr : VExpr vTy finalIsDet finalC)
           -> State Nat Value
unwindValue {vTy} {finalIsDet = False} savedExpr initIdx finalExpr = do
  if dependsOnlyOn initIdx finalExpr
     then do
       case finalExpr of
            (Undet vTy idx) => do
              case decEq initIdx idx of
                   (Yes Refl) => pure $ JustV savedExpr
                   (No _) => state $ \uc => (S uc, JustV $ Undet vTy uc)
            -- TODO: add patterns
            (Op _ _ _) => state $ \uc => (S uc, JustV $ Undet vTy uc)
     else state $ \uc => (S uc, JustV $ Undet vTy uc)
unwindValue {vTy} {finalIsDet = True} savedExpr initIdx finalExpr = pure $ JustV finalExpr

public export
introduceValue : (fr : Value) -> State Nat Value
introduceValue Unkwn = pure Unkwn
introduceValue (JustV {vTy} {isDet = False} vExpr) = state $ \uc => (S uc, JustV $ Undet vTy uc)
introduceValue fr@(JustV {isDet = True} vExpr) = pure fr

public export
unwind' : {n : _}
       -> (savedRegs : _) -> (gs : _) -> (initRegs, finalRegs : _)
       -> AreWinded' {n} savedRegs gs initRegs curUc initUc => CanUnwindAll {n} initRegs gs finalRegs
       => State Nat $ VectValue n
unwind' [] [] [] [] @{AreWindedBase'} @{CanUnwindAllBase} = pure []
unwind' (sr :: savedRegs) (GValue :: gs) (ir :: initRegs) (ir :: finalRegs)
  @{AreWindedStep' @{IsWindedGValue'} areWinded''} @{CanUnwindAllStep @{CanUnwindGValue} canUnwindAll'} = do
    rec <- unwind' savedRegs gs initRegs finalRegs @{areWinded''}
    pure $ sr :: rec
unwind' ((JustV vExpr) :: savedRegs) (GType :: gs) ((JustV $ Undet vTy idx) :: initRegs) ((JustV finalExpr) :: finalRegs)
  @{AreWindedStep' @{IsWindedGType'} areWinded''} @{CanUnwindAllStep @{CanUnwindGType} canUnwindAll'} = do
    r <- unwindValue vExpr idx finalExpr
    rec <- unwind' savedRegs gs initRegs finalRegs @{areWinded''}
    pure $ r :: rec
unwind' (sr :: savedRegs) (GNothing :: gs) (Unkwn :: initRegs) (fr :: finalRegs)
  @{AreWindedStep' @{IsWindedGNothing'} areWinded''} @{CanUnwindAllStep @{CanUnwindGNothing} canUnwindAll'} = do
    r <- introduceValue fr
    rec <- unwind' savedRegs gs initRegs finalRegs @{areWinded''}
    pure $ r :: rec
-- TODO: I have no idea what to do with these covering bugs
unwind' _ _ _ _ = pure never
where
  never : {n : _} -> VectValue n
  never {n = 0} = []
  never {n = S n'} = Unkwn :: never {n = n'}

public export
unwind : {n : _}
      -> (savedRegs : _) -> (savedUc : Nat) -> (gs : _) -> (initRegs, finalRegs : _)
      -> AreWinded {n} savedRegs gs initRegs initUc => CanUnwindAll {n} initRegs gs finalRegs
      => (VectValue n, Nat)
unwind savedRegs savedUc gs initRegs finalRegs @{TheyAreWinded @{areWinded'}} = swap $ runState savedUc $ unwind' savedRegs gs initRegs finalRegs @{areWinded'}

