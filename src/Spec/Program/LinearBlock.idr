module Spec.Program.LinearBlock

import public Spec.Context.Loop.Misc
import public Spec.Program.Loop.Decision.Close
import public Debug.Trace

%default total

-- Complexity: O(n + #GValue * n) = O(n^2)
public export
isSuitable : (finalRegs : VectValue n) ->
             {ols : ListLoop n} ->
             CloseLoopDecision remSrcs ols ->
             Bool
isSuitable finalRegs {ols = []} _ = True
isSuitable finalRegs {ols = ((L savedRegs savedSrcs savedUc gs initRegs @{areWinded}) :: ols)} _ =
  hasUndetIDependsOnlyOnInit initRegs @{areWinded} finalRegs
  && areGuaranteesWeaklyPreserved gs initRegs @{areWinded} finalRegs
  && (hasMonotonicValue finalRegs || canMakeMonotonicValue finalRegs)

public export
data FusedProduce : (vop : ValueOp) ->
                    (cLim : Nat) ->
                    (regs : VectValue n) ->
                    {-target-}Fin n ->
                    {-v-}Value ->
                    Type where
  MkFusedProduce : Produce vop cLim regs v => FusedProduce vop cLim regs target v

public export
data CanFinish : {0 remSrcs : VectSource l n} ->
                 (closeDec : CloseLoopDecision remSrcs ols) ->
                 (finalRegs : VectValue n) ->
                 Type where
  CanSimplyFinish : CanFinish NoClose finalRegs
  MustFinishLoop : CanUnwindAll initRegs gs finalRegs =>
                   So (hasMonotonicValue finalRegs) =>
                   CanFinish (DoClose $ L savedRegs savedSrcs savedUc gs initRegs @{areWinded}) finalRegs

{-
There are 3 kinds of LinearBlock:
 - no loops => no restrictions
 - has a loop, but not closing => weak restrictions
 - has a loop, closing => strong restrictions (weak + must be able to unwind)
-}
public export
data LinearBlock : (cLim : Nat) ->
                   {0 l : _} ->
                   {0 remSrcs : VectSource l n} ->
                   {0 ols : ListLoop n} ->
                   (closeDec : CloseLoopDecision {n} remSrcs ols) ->
                   (regs : VectValue n) ->
                   {-finalRegs-}VectValue n ->
                   Type where

  Assign : {0 n, l : _} ->
           {0 cLim : _} ->
           {0 remSrcs : VectSource l n} ->
           {0 ols : ListLoop n} ->
           {0 closeDec : CloseLoopDecision remSrcs ols} ->
           {0 regs : VectValue n} ->
           {0 finalRegs : VectValue n} ->
           (target, i : Fin n) ->
           NotSame target i =>
           let 0 contRegs : ?; contRegs = duplicate target i regs in
           So (isSuitable contRegs closeDec) =>
           LinearBlock cLim closeDec contRegs finalRegs ->
           LinearBlock cLim closeDec regs finalRegs

  RegOp : {0 n, l : _} ->
          {0 cLim : _} ->
          {0 remSrcs : VectSource l n} ->
          {0 ols : ListLoop n} ->
          {0 closeDec : CloseLoopDecision remSrcs ols} ->
          {0 regs : VectValue n} ->
          {0 v : _} ->
          {0 finalRegs : VectValue n} ->
          (vop : ValueOp) -> (target : Fin n) ->
          FusedProduce vop cLim regs target v =>
          let 0 contRegs : ?; contRegs = replaceAt target v regs in
          So (isSuitable contRegs closeDec) =>
          LinearBlock cLim closeDec contRegs finalRegs ->
          LinearBlock cLim closeDec regs finalRegs

  Finish : CanFinish closeDec regs =>
           LinearBlock cLim closeDec regs regs

public export
getCanFinish : LinearBlock cLim closeDec regs finalRegs -> CanFinish closeDec finalRegs
getCanFinish (Assign _ _ cont) = getCanFinish cont
getCanFinish (RegOp _ _ cont) = getCanFinish cont
getCanFinish (Finish @{canFinish}) = canFinish

