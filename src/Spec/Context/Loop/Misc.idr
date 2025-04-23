module Spec.Context.Loop.Misc

import public Spec.Value.Misc
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
areGuaranteesWeaklyPreserved' : (gs : VectGuarantee n) ->
                                (initRegs : VectValue n) ->
                                AreWinded' savedRegs gs initRegs uc initUc =>
                                (finalRegs : VectValue m) ->
                                Bool
areGuaranteesWeaklyPreserved' [] [] finalRegs = True
areGuaranteesWeaklyPreserved' (GValue :: gs) (ir :: initRegs) @{AreWindedStep' @{IsWindedGValue'} areWinded''} finalRegs =
  (contains ir finalRegs) && areGuaranteesWeaklyPreserved' gs initRegs @{areWinded''} finalRegs
  where
    contains : forall m . Value -> VectValue m -> Bool
    contains v [] = False
    contains v (v1 :: vs) = (isYes $ decEq v v1) || contains v vs
areGuaranteesWeaklyPreserved' (GType :: gs) ((JustV $ Undet initVTy initIdx) :: initRegs) @{AreWindedStep' @{IsWindedGType'} areWinded''} finalRegs =
  (contains initVTy finalRegs) && areGuaranteesWeaklyPreserved' gs initRegs @{areWinded''} finalRegs
  where
    contains : forall m . VType -> VectValue m -> Bool
    contains _ [] = False
    contains vTy (Unkwn :: vs) = contains vTy vs
    contains vTy ((JustV {vTy=vTy'} vExpr) :: vs) = (isYes $ decEq vTy vTy') || contains vTy vs
areGuaranteesWeaklyPreserved' (GNothing :: gs) (Unkwn :: initRegs) @{AreWindedStep' @{IsWindedGNothing'} areWinded''} finalRegs =
  areGuaranteesWeaklyPreserved' gs initRegs @{areWinded''} finalRegs
areGuaranteesWeaklyPreserved' _ _ _ = False

public export
areGuaranteesWeaklyPreserved : (gs : VectGuarantee n) ->
                               (initRegs : VectValue n) ->
                               AreWinded savedRegs gs initRegs initUc =>
                               (finalRegs : VectValue m) ->
                               Bool
areGuaranteesWeaklyPreserved gs initRegs @{TheyAreWinded @{areWinded'}} finalRegs =
  areGuaranteesWeaklyPreserved' gs initRegs @{areWinded'} finalRegs




public export
isUndetIDependsOnlyOn : (idx : Nat) -> (fr : Value) -> Bool
isUndetIDependsOnlyOn idx Unkwn = False
isUndetIDependsOnlyOn idx (JustV {isDet} vExpr) = (not isDet) && dependsOnlyOn idx vExpr

public export
hasUndetIDependsOnlyOn : (idx : Nat) -> (finalRegs : VectValue m) -> Bool
hasUndetIDependsOnlyOn _ [] = False
hasUndetIDependsOnlyOn idx (fr :: finalRegs) =
  isUndetIDependsOnlyOn idx fr || hasUndetIDependsOnlyOn idx finalRegs

public export
hasUndetIDependsOnlyOnThis : (ir : Value) ->
                             IsWinded' sr g ir uc initUc =>
                             (finalRegs : VectValue n) ->
                             Bool
hasUndetIDependsOnlyOnThis (JustV $ Undet vTy i)
                           @{IsWindedGValue' @{IsWindedUndet'}}
                           finalRegs = hasUndetIDependsOnlyOn i finalRegs
hasUndetIDependsOnlyOnThis (JustV $ Undet vTy i)
                           @{IsWindedGType'}
                           finalRegs = hasUndetIDependsOnlyOn i finalRegs
hasUndetIDependsOnlyOnThis (JustV _)
                           @{IsWindedGValue' @{IsWindedDet'}}
                           finalRegs = False
hasUndetIDependsOnlyOnThis Unkwn
                           @{IsWindedGNothing'}
                           finalRegs = False
hasUndetIDependsOnlyOnThis _ _ = trace "Unreachable!!" False

public export
hasUndetIDependsOnlyOnInit' : (initRegs : VectValue n) ->
                              AreWinded' savedRegs gs initRegs uc initUc =>
                              (finalRegs : VectValue m) ->
                              Bool
hasUndetIDependsOnlyOnInit' [] @{AreWindedBase'} _ = False
hasUndetIDependsOnlyOnInit' (ir :: initRegs) @{AreWindedStep' @{isWinded'} areWinded''} finalRegs =
  hasUndetIDependsOnlyOnThis ir @{isWinded'} finalRegs || hasUndetIDependsOnlyOnInit' initRegs @{areWinded''} finalRegs

-- Checks that there's an undet value that depends on an init value at any place of finalRegs
public export
hasUndetIDependsOnlyOnInit : (initRegs : VectValue n) ->
                             AreWinded savedRegs gs initRegs initUc =>
                             (finalRegs : VectValue m) ->
                             Bool
hasUndetIDependsOnlyOnInit initRegs @{TheyAreWinded @{areWinded'}} finalRegs =
  hasUndetIDependsOnlyOnInit' initRegs @{areWinded'} finalRegs

public export
canMakeMonotonicValue : (regs : VectValue n) -> Bool
canMakeMonotonicValue regs =
  hasDetIValue regs && hasPureUndetIValue regs
  where
    hasDetIValue : forall n . VectValue n -> Bool
    hasDetIValue [] = False
    hasDetIValue (r :: regs) = isDetIValue r || hasDetIValue regs
      where
        isDetIValue : Value -> Bool
        isDetIValue Unkwn = False
        isDetIValue (JustV {vTy} {isDet = False} vExpr) = False
        isDetIValue (JustV {vTy = I} {isDet = True} vExpr) = True
        isDetIValue (JustV {vTy = B} {isDet = True} vExpr) = False

    hasPureUndetIValue : forall n . VectValue n -> Bool
    hasPureUndetIValue [] = False
    hasPureUndetIValue (r :: regs) = isPureUndetIValue r || hasPureUndetIValue regs
      where
        isPureUndetIValue : Value -> Bool
        isPureUndetIValue Unkwn = False
        isPureUndetIValue (JustV $ Det _) = False
        isPureUndetIValue (JustV $ Undet I _) = True
        isPureUndetIValue (JustV $ Undet B _) = False
        isPureUndetIValue (JustV $ Op _ _ _) = False

public export
data IsMonotonic : Value -> Type where
  ItIsMonotonic1 : IsMonotonic (JustV $ Op Add (Undet I idx) (Det $ RawI a) @{ovtPrf} @{boolAndPrf} @{natSumPrf})
  ItIsMonotonic2 : IsMonotonic (JustV $ Op Add (Det $ RawI a) (Undet I idx) @{ovtPrf} @{boolAndPrf} @{natSumPrf})

public export
getIndex : (v : Value) -> IsMonotonic v => Nat
getIndex (JustV $ Op Add (Undet I idx) (Det $ RawI a)) @{ItIsMonotonic1} = idx
getIndex (JustV $ Op Add (Det $ RawI a) (Undet I idx)) @{ItIsMonotonic2} = idx

public export
isMonotonicValue : Value -> Bool
isMonotonicValue (JustV $ Op Add (Undet I idx) (Det $ RawI a)) = True
isMonotonicValue (JustV $ Op Add (Det $ RawI a) (Undet I idx)) = True
isMonotonicValue _ = False

public export
hasMonotonicValue : (regs : VectValue n) -> Bool
hasMonotonicValue [] = False
hasMonotonicValue (r :: regs) = isMonotonicValue r || hasMonotonicValue regs
    



public export
unwindValue : {vTy : _} ->
              {isDet, finalIsDet : _} ->
              {c, finalC : _} ->
              (savedExpr : VExpr vTy isDet c) ->
              (initIdx : Nat) ->
              (finalExpr : VExpr vTy finalIsDet finalC) ->
              State Nat Value
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
unwind' : {n : _} ->
          (savedRegs : _) ->
          (gs : _) ->
          (initRegs, finalRegs : _) ->
          AreWinded' {n} savedRegs gs initRegs curUc initUc =>
          CanUnwindAll {n} initRegs gs finalRegs =>
          State Nat $ VectValue n
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
-- TODO: compiler covering bug
unwind' _ _ _ _ = pure never
where
  never : {n : _} -> VectValue n
  never {n = 0} = []
  never {n = S n'} = Unkwn :: never {n = n'}

public export
unwind : {n : _} ->
         (savedRegs : _) ->
         (savedUc : Nat) ->
         (gs : _) ->
         (initRegs, finalRegs : _) ->
         AreWinded {n} savedRegs gs initRegs initUc =>
         CanUnwindAll {n} initRegs gs finalRegs =>
         (VectValue n, Nat)
unwind savedRegs savedUc gs initRegs finalRegs @{TheyAreWinded @{areWinded'}} = swap $ runState savedUc $ unwind' savedRegs gs initRegs finalRegs @{areWinded'}

