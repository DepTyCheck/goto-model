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

-- check that there's an undet value that depends on some initRegs value at any place of the registers
public export
hasUndetDependsOnlyOnInit : (initRegs : VectValue n)
                                 -> AreWinded savedRegs gs initRegs initUc
                                 => (finalRegs : VectValue m)
                                 -> Bool
hasUndetDependsOnlyOnInit initRegs @{TheyAreWinded @{areWinded'}} finalRegs =
  hasUndetDependsOnlyOnInit' initRegs @{areWinded'} finalRegs

-- Complexity: O(n + #GValue * n) = O(n^2)
public export
isSuitable : (finalRegs : VectValue n)
          -> {ols : ListLoop n}
          -> CloseLoopDecision remSrcs ols
          -> Bool
isSuitable finalRegs {ols = []} _ = True
isSuitable finalRegs {ols = ((L savedRegs savedSrcs savedUc gs initRegs @{areWinded}) :: ols)} _ =
  hasUndetDependsOnlyOnInit initRegs @{areWinded} finalRegs && areGuaranteesWeaklyPreserved gs initRegs finalRegs

public export  -- 7
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
  MustFinishLoop : CanUnwindAll initRegs gs finalRegs => CanFinish (DoClose $ L savedRegs savedSrcs savedUc gs initRegs @{areWinded}) finalRegs

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

