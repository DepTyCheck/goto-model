module Spec.Program.Edges

import public Spec.Context.Source
import public Spec.Program.Loop.Decision.Close

%default total

public export
data IsExitPossible : CloseLoopDecision remSrcs ols -> Type where
  ExitIsPossibleNoLoops : IsExitPossible {ols=[]} NoClose

public export
data EdgeDecision : CloseLoopDecision remSrcs ols -> Type where
  Exit : IsExitPossible closeDec => EdgeDecision closeDec
  Jmp : EdgeDecision closeDec
  -- TODO: condjmp is only possible then we can end the loop or there's no loop but 1 undet value
  Condjmp : EdgeDecision closeDec

%name EdgeDecision edgeDec

public export
record Result (n : Nat) where
  constructor R
  contImmSrc : MaybeSource n
  contDelaSrc : MaybeSource n
  contSrcsLen : Nat
  contSrcs : VectSource contSrcsLen n

public export
makeEdges : {closeDec : CloseLoopDecision {n} _ _}
         -> EdgeDecision closeDec
         -> {l : _}
         -> (srcs : VectSource l n)
         -> (finalRegs : VectValue n)
         -> Result n
makeEdges Exit srcs finalRegs =
  R Nothing Nothing _ srcs
makeEdges {closeDec = NoClose} Jmp srcs finalRegs =
  R Nothing Nothing _ (Src finalRegs :: srcs)
makeEdges {closeDec = (DoClose _)} Jmp srcs finalRegs =
  R Nothing Nothing _ srcs
makeEdges {closeDec = NoClose} Condjmp srcs finalRegs =
  R (Just $ Src finalRegs) (Just $ Src finalRegs) _ srcs
makeEdges {closeDec = (DoClose _)} Condjmp srcs finalRegs =
  R Nothing Nothing _ (Src finalRegs :: srcs)

