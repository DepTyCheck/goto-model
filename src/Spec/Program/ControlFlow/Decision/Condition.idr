module Spec.Program.ControlFlow.Decision.Condition

import public Spec.Program.Loop.Variant

%default total

public export
data PrimaryPredicate : (vTy : VType) -> Type where
  LessThan : PrimaryPredicate I
  Equal : PrimaryPredicate I
  LessThanOrEqual : PrimaryPredicate I
  IsTrue : PrimaryPredicate B

public export
data PredicateConstant : PrimaryPredicate vTy -> Type where
  NoConstant : PredicateConstant IsTrue
  Constant : {0 p : PrimaryPredicate I} -> Nat -> PredicateConstant p

public export
data Condition : {0 closeDec : CloseLoopDecision remSrcs ols} ->
                 {0 canFinish : CanFinish closeDec finalRegs} ->
                 (varDec : VariantDecision closeDec finalRegs canFinish Condjmp) ->
                 Type where
  ConditionAny : {0 remSrcs : VectSource l n} ->
                 {0 ols : ListLoop n} ->
                 {0 hasVariantPrf : HasVariant finalRegs} ->
                 {0 canFinish : CanFinish NoClose finalRegs} ->
                 (p : PrimaryPredicate (getVType hasVariantPrf)) ->
                 PredicateConstant p ->
                 Condition {canFinish} (VariantNoCloseCondjmp {remSrcs} {ols} @{hasVariantPrf})
  ConditionDoClose : {0 hasLoopVariantPrf : HasLoopVariant initRegs areWinded' finalRegs canUnwindAll Condjmp} ->
                     (p : PrimaryPredicate I) ->
                     PredicateConstant p ->
                     Condition {closeDec = DoClose $ L savedRegs savedSrcs savedUc gs initRegs @{TheyAreWinded @{areWinded'}}}
                               (VariantDoClose @{hasLoopVariantPrf})
  
public export
data ConditionDecision : {0 closeDec : CloseLoopDecision a b} ->
                         {0 canFinish : CanFinish closeDec finalRegs} ->
                         (edgeDec : EdgeDecision closeDec) ->
                         (varDec : VariantDecision closeDec finalRegs canFinish edgeDec) ->
                         Type where
  NoCondition : {0 varDec : VariantDecision closeDec finalRegs canFinish edgeDec} ->
                NotCondjmp edgeDec =>
                ConditionDecision edgeDec varDec
  HasCondition : {0 varDec : VariantDecision closeDec finalRegs canFinish Condjmp} ->
                 Condition varDec ->
                 (neg : Bool) ->
                 ConditionDecision Condjmp varDec

public export
record Result (n : Nat) where
  constructor R
  contImmSrc : MaybeSource n
  contDelaSrc : MaybeSource n
  contSrcsLen : Nat
  contSrcs : VectSource contSrcsLen n

-- now, make edges using
-- EdgeDecision
-- VariantDecision
-- ConditionDecision
public export
makeEdges : {closeDec : CloseLoopDecision {n} _ _} ->
            EdgeDecision closeDec ->
            {l : _} ->
            (srcs : VectSource l n) ->
            (finalRegs : VectValue n) ->
            Result n
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

