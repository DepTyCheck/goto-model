module Spec.Program.Edge

import public Spec.Program.LinearBlock

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

namespace Exit
  public export
  data IsExitPossible : (closeDec : CloseLoopDecision remSrcs ols) -> Type where
    ItIsPossibleNoLoops : IsExitPossible {ols=[]} NoClose

namespace Jmp
  public export
  data IsJmpPossible : (closeDec : CloseLoopDecision remSrcs ols) -> Type where
    ItIsPossibleNoClose : IsJmpPossible {ols=[]} NoClose
    -- TODO: it is possible to close loop with a jmp instruction,
    --   but we need to check if there's a source depending on a loop variant

namespace Condjmp
  public export
  isUndetIDependsOnlyOnSelf : (ir : Value) ->
                              IsWinded' sr g ir uc initUc =>
                              (fr : Value) ->
                              Bool
  isUndetIDependsOnlyOnSelf (JustV $ Undet vTy i) @{IsWindedGValue' @{IsWindedUndet'}} fr = isUndetIDependsOnlyOn i fr
  isUndetIDependsOnlyOnSelf (JustV vExpr)         @{IsWindedGValue' @{IsWindedDet'}}   fr = False
  isUndetIDependsOnlyOnSelf (JustV $ Undet vTy i) @{IsWindedGType'}                    fr = isUndetIDependsOnlyOn i fr
  isUndetIDependsOnlyOnSelf Unkwn                 @{IsWindedGNothing'}                 fr = False
  isUndetIDependsOnlyOnSelf _ _ = False

  public export
  data HasLoopVariant : (initRegs : VectValue k) ->
                        (areWinded' : AreWinded' savedRegs gs initRegs uc initUc) ->
                        (finalRegs : VectValue k) ->
                        (canUnwindAll : CanUnwindAll initRegs gs finalRegs) ->
                        Type where
    Here : {0 areWinded'' : AreWinded' savedRegs gs initRegs uc initUc} ->
           IsMonotonic fr =>
           So (isUndetIDependsOnlyOnSelf ir @{isWinded'} fr) =>
           HasLoopVariant (ir :: initRegs)
                          (AreWindedStep' @{isWinded'} areWinded'')
                          (fr :: finalRegs)
                          (CanUnwindAllStep @{canUnwind} canUnwindAll')
    There : HasLoopVariant initRegs
                           areWinded''
                           finalRegs
                           canUnwindAll' ->
            HasLoopVariant (ir :: initRegs)
                           (AreWindedStep' @{isWinded'} areWinded'')
                           (fr :: finalRegs)
                           (CanUnwindAllStep @{canUnwind} canUnwindAll')

  public export
  data IsCondjmpPossible : (closeDec : CloseLoopDecision {n} remSrcs ols) ->
                           (finalRegs : VectValue n) ->
                           (canFinish : CanFinish closeDec finalRegs) ->
                           Type where
    ItIsPossibleNoClose : So (hasUndet finalRegs) =>
                          IsCondjmpPossible {remSrcs} {ols} NoClose finalRegs canFinish
    ItIsPossibleDoCloseWithVariant : HasLoopVariant initRegs areWinded' finalRegs canUnwindAll =>
                                     IsCondjmpPossible (DoClose {n} {ols} $ L savedRegs
                                                                              savedSrcs
                                                                              savedUc
                                                                              gs
                                                                              initRegs
                                                                              @{TheyAreWinded @{areWinded'}})
                                                       finalRegs
                                                       (MustFinishLoop @{canUnwindAll} @{so})
    -- TODO: it is possible to close loop with a condjmp instruction without variant in a condition,
    --   but we need to check if there's a source depending on a loop variant

  namespace Condition
    public export
    data IsPossibleWithoutVariant : IsCondjmpPossible closeDec finalRegs canFinish -> Type where
      ItIsItIsPossibleNoClose : IsPossibleWithoutVariant $ ItIsPossibleNoClose @{so}
      -- TODO: 1 more constructor when todo above is solved

    public export
    data PrimaryPredicate : (vTy : VType) -> Type where
      LessThan : PrimaryPredicate I
      Equal : PrimaryPredicate I
      LessThanOrEqual : PrimaryPredicate I
      IsTrue : PrimaryPredicate B

    public export
    data PredicateConstant : PrimaryPredicate vTy -> Type where
      NoConstant : PredicateConstant IsTrue
      Constant : {0 pp : PrimaryPredicate I} -> Nat -> PredicateConstant pp

    public export
    getVType : {vs : _} -> HasUndet vs -> VType
    getVType {vs = (JustV {vTy} _ :: _)} HasUndetHere = vTy
    getVType (HasUndetThere prf') = getVType prf'
  
    public export
    data Condition : {0 closeDec : CloseLoopDecision {n} remSrcs ols} ->
                     (finalRegs : VectValue n) ->
                     {0 canFinish : CanFinish closeDec finalRegs} ->
                     IsCondjmpPossible closeDec finalRegs canFinish ->
                     Type where
      ConditionAny : IsPossibleWithoutVariant possiblePrf =>
                     (condRegIdx : HasUndet finalRegs) ->
                     (pp : PrimaryPredicate (getVType condRegIdx)) ->
                     PredicateConstant pp ->
                     (neg : Bool) ->
                     Condition finalRegs possiblePrf
      ConditionVar : {0 hasLoopVariant : HasLoopVariant initRegs areWinded' finalRegs canUnwindAll} ->
                     (varRegIdx : HasLoopVariant initRegs areWinded' finalRegs canUnwindAll) ->
                     (pp : PrimaryPredicate I) ->
                     PredicateConstant pp ->
                     (neg : Bool) ->
                     Condition finalRegs $
                               ItIsPossibleDoCloseWithVariant {n}
                                                              {ols}
                                                              {savedRegs}
                                                              {savedSrcs}
                                                              {so}
                                                              @{hasLoopVariant}

public export
data EdgeDecision : (closeDec : CloseLoopDecision {n} remSrcs ols) ->
                    (finalRegs : VectValue n) ->
                    CanFinish closeDec finalRegs ->
                    Type where
  Exit : IsExitPossible closeDec =>
         EdgeDecision closeDec finalRegs canFinish
  Jmp : IsJmpPossible closeDec =>
        EdgeDecision closeDec finalRegs canFinish
  Condjmp : (possiblePrf : IsCondjmpPossible closeDec finalRegs canFinish) =>
            Condition finalRegs possiblePrf ->
            EdgeDecision closeDec finalRegs canFinish

%name EdgeDecision edgeDec

public export
record Result (n : Nat) where
  constructor R
  contImmSrc : MaybeSource n
  contDelaSrc : MaybeSource n
  contSrcsLen : Nat
  contSrcs : VectSource contSrcsLen n

public export
makeEdges : {closeDec : CloseLoopDecision {n} _ _} ->
            {canFinish : CanFinish closeDec finalRegs'} ->
            EdgeDecision closeDec finalRegs' canFinish ->
            {l : _} ->
            (srcs : VectSource l n) ->
            (finalRegs : VectValue n) ->
            Result n
makeEdges Exit srcs finalRegs = R Nothing Nothing _ srcs
makeEdges {closeDec = NoClose} Jmp srcs finalRegs = R Nothing Nothing _ (Src finalRegs :: srcs)
makeEdges {closeDec = (DoClose _)} Jmp srcs finalRegs = R Nothing Nothing _ srcs
makeEdges {closeDec = NoClose} (Condjmp _) srcs finalRegs = R (Just $ Src finalRegs) (Just $ Src finalRegs) _ srcs
makeEdges {closeDec = (DoClose _)} (Condjmp _) srcs finalRegs = R Nothing Nothing _ (Src finalRegs :: srcs)

