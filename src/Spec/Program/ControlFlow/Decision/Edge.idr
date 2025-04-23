module Spec.Program.ControlFlow.Decision.Edge

import public Spec.Program.Loop.Decision.Close

%default total

{-
No loops:
  exit, jmp: nothing
  condjmp: undet register value to make a condition

Has loop, not closing:
  exit: impossible
  jmp: nothing
  condjmp: undet register value to make a condition

Has loop, closing:
  exit: impossible
  jmp: need an undet self-depending value
       there's locked source with value in cond which expression is a subexpression of the counter
  condjmp: need an undet self-depending value
-}

public export
data IsExitPossible : (closeDec : CloseLoopDecision remSrcs ols) -> Type where
  ExitIsPossibleNoLoops : IsExitPossible {ols=[]} NoClose

public export
data EdgeDecision : (closeDec : CloseLoopDecision remSrcs ols) -> Type where
  Exit : IsExitPossible closeDec => EdgeDecision closeDec
  Jmp : EdgeDecision closeDec
  Condjmp : EdgeDecision closeDec

%name EdgeDecision edgeDec

public export
data NotCondjmp : EdgeDecision closeDec -> Type where
  ItIsExit : NotCondjmp (Exit @{exitPossible})
  ItIsJmp : NotCondjmp Jmp

