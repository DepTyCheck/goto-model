module Spec.Program.LinearBlock

import public Spec.Value
import public Spec.Context.Loop.Misc
import public Spec.Program.Loop.Decision.Close
import public Debug.Trace

%default total

public export
hasUndetDependsOnlyOnThis : (idx : Nat) -> (finalRegs : VectValue m) -> Bool
hasUndetDependsOnlyOnThis _ [] = False
hasUndetDependsOnlyOnThis idx (Unkwn :: finalRegs) =
  hasUndetDependsOnlyOnThis idx finalRegs
hasUndetDependsOnlyOnThis idx ((JustV {isDet = False} vExpr) :: finalRegs) =
  dependsOnlyOn idx vExpr || hasUndetDependsOnlyOnThis idx finalRegs
hasUndetDependsOnlyOnThis idx ((JustV {isDet = True} vExpr) :: finalRegs) =
  hasUndetDependsOnlyOnThis idx finalRegs

public export
hasUndetDependsOnlyOnInit' : (initRegs : VectValue n)
                          -> AreWinded' savedRegs gs initRegs uc initUc
                          => (finalRegs : VectValue m)
                          -> Bool
hasUndetDependsOnlyOnInit' [] @{AreWindedBase'} _ = False
hasUndetDependsOnlyOnInit' ((JustV _) :: initRegs) @{AreWindedStep' @{IsWindedGValue' @{IsWindedDet'}} areWinded''} finalRegs =
  hasUndetDependsOnlyOnInit' initRegs @{areWinded''} finalRegs
hasUndetDependsOnlyOnInit' (Unkwn :: initRegs) @{AreWindedStep' @{IsWindedGNothing'} areWinded''} finalRegs =
  hasUndetDependsOnlyOnInit' initRegs @{areWinded''} finalRegs
hasUndetDependsOnlyOnInit' ((JustV $ Undet vTy i) :: initRegs) @{AreWindedStep' @{IsWindedGValue' @{IsWindedUndet'}} areWinded''} finalRegs =
  hasUndetDependsOnlyOnThis i finalRegs
hasUndetDependsOnlyOnInit' ((JustV $ Undet vTy i) :: initRegs) @{AreWindedStep' @{IsWindedGType'} areWinded''} finalRegs =
  hasUndetDependsOnlyOnThis i finalRegs
hasUndetDependsOnlyOnInit' (_ :: _) _ = trace "Unreachable!" False

-- Checks that there's an undet value that depends on an init value at any place of finalRegs
public export
hasUndetDependsOnlyOnInit : (initRegs : VectValue n)
                         -> AreWinded savedRegs gs initRegs initUc
                         => (finalRegs : VectValue m)
                         -> Bool
hasUndetDependsOnlyOnInit initRegs @{TheyAreWinded @{areWinded'}} finalRegs =
  hasUndetDependsOnlyOnInit' initRegs @{areWinded'} finalRegs

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
hasMonotonicValue : (regs : VectValue n) -> Bool
hasMonotonicValue [] = False
hasMonotonicValue (r :: regs) = isMonotonicValue r || hasMonotonicValue regs
  where
    isMonotonicValue : Value -> Bool
    isMonotonicValue (JustV $ Op Add (Undet I idx) (Det $ RawI a)) = True
    isMonotonicValue (JustV $ Op Add (Det $ RawI a) (Undet I idx)) = True
    isMonotonicValue _ = False

-- Complexity: O(n + #GValue * n) = O(n^2)
public export
isSuitable : (finalRegs : VectValue n)
          -> {ols : ListLoop n}
          -> CloseLoopDecision remSrcs ols
          -> Bool
isSuitable finalRegs {ols = []} _ = True
isSuitable finalRegs {ols = ((L savedRegs savedSrcs savedUc gs initRegs @{areWinded}) :: ols)} _ =
  hasUndetDependsOnlyOnInit initRegs @{areWinded} finalRegs
  && areGuaranteesWeaklyPreserved gs initRegs finalRegs
  && (hasMonotonicValue finalRegs || canMakeMonotonicValue finalRegs)

public export
data FusedProduce : (vop : ValueOp)
                 -> (cLim : Nat)
                 -> (regs : VectValue n)
                 -> {-target-}Fin n
                 -> {-v-}Value
                 -> Type where
  MkFusedProduce : Produce vop cLim regs v => FusedProduce vop cLim regs target v

public export
data CanFinish : {0 remSrcs : VectSource l n}
              -> (closeDec : CloseLoopDecision remSrcs ols)
              -> (finalRegs : VectValue n)
              -> Type where
  CanSimplyFinish : CanFinish NoClose finalRegs
  MustFinishLoop : CanUnwindAll initRegs gs finalRegs
                => So (hasMonotonicValue finalRegs)
                => CanFinish (DoClose $ L savedRegs savedSrcs savedUc gs initRegs @{areWinded}) finalRegs

{-
There are 3 kinds of LinearBlock:
 - no loops => no restrictions
 - has a loop, but not closing => weak restrictions
 - has a loop, closing => strong restrictions (weak + must be able to unwind)
-}
public export
data LinearBlock : (cLim : Nat)
                -> {0 l : _}
                -> {0 remSrcs : VectSource l n}
                -> {0 ols : ListLoop n}
                -> (closeDec : CloseLoopDecision {n} remSrcs ols)
                -> (regs : VectValue n)
                -> {-finalRegs-}VectValue n
                -> Type where

  Assign : {0 n, l : _}
        -> {0 cLim : _}
        -> {0 remSrcs : VectSource l n}
        -> {0 ols : ListLoop n}
        -> {0 closeDec : CloseLoopDecision remSrcs ols}
        -> {0 regs : VectValue n}
        -> {0 finalRegs : VectValue n}
        -> (target, i : Fin n)
        -> NotSame target i
        => let 0 contRegs : ?; contRegs = duplicate target i regs in
           So (isSuitable contRegs closeDec)
        => LinearBlock cLim closeDec contRegs finalRegs
        -> LinearBlock cLim closeDec regs finalRegs

  RegOp : {0 n, l : _}
       -> {0 cLim : _}
       -> {0 remSrcs : VectSource l n}
       -> {0 ols : ListLoop n}
       -> {0 closeDec : CloseLoopDecision remSrcs ols}
       -> {0 regs : VectValue n}
       -> {0 v : _}
       -> {0 finalRegs : VectValue n}
       -> (vop : ValueOp) -> (target : Fin n)
       -> FusedProduce vop cLim regs target v
       => let 0 contRegs : ?; contRegs = replaceAt target v regs in
          So (isSuitable contRegs closeDec)
       => LinearBlock cLim closeDec contRegs finalRegs
       -> LinearBlock cLim closeDec regs finalRegs

  Finish : CanFinish closeDec regs
        => LinearBlock cLim closeDec regs regs

public export
getCanFinish : LinearBlock cLim closeDec regs finalRegs -> CanFinish closeDec finalRegs
getCanFinish (Assign _ _ cont) = getCanFinish cont
getCanFinish (RegOp _ _ cont) = getCanFinish cont
getCanFinish (Finish @{canFinish}) = canFinish

