module Spec.Program.Edges

import public Spec.Context.Source

%default total

public export
data EdgeDecision : {-hasLoop and canEnd = Just True-}MaybeBool -> Type where
  Exit : NotJustFalse loopState => EdgeDecision loopState
  Jmp : EdgeDecision loopState
  -- TODO: condjmp is only possible then we can end the loop or there's no loop but 1 undet value
  Condjmp : EdgeDecision loopState

%name EdgeDecision edgeDec

public export
record Result (n : Nat) where
  constructor R
  contImmSrc : MaybeSource n
  contDelaSrc : MaybeSource n
  contSrcsLen : Nat
  contSrcs : VectSource contSrcsLen n

public export
makeEdges : {mb : _} -> EdgeDecision mb -> {l : _} -> (srcs : VectSource l n) -> (finalRegs : VectValue n)
         -> Edges.Result n
makeEdges {mb} (Exit @{notJustFalse}) srcs finalRegs = R Nothing Nothing _ srcs
makeEdges {mb} Jmp srcs finalRegs = do
  case mb of
       (Just True) => R Nothing Nothing _ srcs
       _ => R Nothing Nothing _ (Src finalRegs :: srcs)
makeEdges {mb} Condjmp srcs finalRegs = do
  case mb of
       (Just True) => R Nothing Nothing _ (Src finalRegs :: srcs)
       _ => R (Just $ Src finalRegs) (Just $ Src finalRegs) _ srcs
