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
    ItIsPossibleNoClose : IsJmpPossible NoClose
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
  isLoopVariantAt : (i : Fin n) ->
                  (initRegs : VectValue n) ->
                  AreWinded' savedRegs gs initRegs uc initUc =>
                  (finalRegs : VectValue n) ->
                  CanUnwindAll initRegs gs finalRegs =>
                  Bool
  isLoopVariantAt FZ
                (ir :: initRegs)
                @{AreWindedStep' @{isWinded'} areWinded''}
                (fr :: finalRegs)
                @{CanUnwindAllStep @{canUnwind} canUnwindAll'} = isUndetIDependsOnlyOnSelf ir @{isWinded'} fr
  isLoopVariantAt (FS i')
                (_ :: initRegs)
                @{AreWindedStep' areWinded''}
                (_ :: finalRegs)
                @{CanUnwindAllStep canUnwindAll'} = isLoopVariantAt i' initRegs @{areWinded''} finalRegs

  namespace Condition
    public export
    getVType  : (vs : VectValue n) -> HasUndetAt i vs -> VType
    getVType (JustV {vTy} _ :: _) HasUndetAtHere = vTy
    getVType (_ :: vs) (HasUndetAtThere prf') = getVType vs prf'

    public export
    data Condition : (closeDec : CloseLoopDecision {n} remSrcs ols) ->
                     (finalRegs : VectValue n) ->
                     (canFinish : CanFinish closeDec finalRegs) ->
                     Type where
      ConditionAny : (regIdx : Fin n) ->
                     (undetPrf : HasUndetAt regIdx finalRegs) =>
                     (pp : PrimaryPredicate (getVType finalRegs undetPrf)) ->
                     PredicateConstant pp ->
                     (neg : Bool) ->
                     Condition {remSrcs} {ols} NoClose finalRegs canFinish
      ConditionVar : (regIdx : Fin n) ->
                     So (isLoopVariantAt regIdx initRegs @{areWinded'} finalRegs @{canUnwindAll}) =>
                     HasTypeAt regIdx I finalRegs =>  -- Helping
                     (pp : PrimaryPredicate I) ->
                     PredicateConstant pp ->
                     (neg : Bool) ->
                     Condition (DoClose {n} {ols} $ L savedRegs
                                                      savedSrcs
                                                      savedUc
                                                      gs
                                                      initRegs
                                                      @{TheyAreWinded @{areWinded'}})
                               finalRegs
                               (MustFinishLoop @{canUnwindAll} @{so})
      -- TODO: it is possible to close loop with a condjmp instruction without variant in a condition,
      --   but we need to check if there's a source depending on a loop variant

public export
data EdgeDecision : (closeDec : CloseLoopDecision {n} remSrcs ols) ->
                    (finalRegs : VectValue n) ->
                    (canFinish : CanFinish closeDec finalRegs) ->
                    Type where
  Exit : IsExitPossible closeDec =>
         EdgeDecision closeDec finalRegs canFinish
  Jmp : IsJmpPossible closeDec =>
        EdgeDecision closeDec finalRegs canFinish
  Condjmp : Condition closeDec finalRegs canFinish ->
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
makeEdges {closeDec = NoClose} Jmp srcs finalRegs = R Nothing Nothing _ (Src finalRegs Nothing :: srcs)
makeEdges {closeDec = (DoClose _)} Jmp srcs finalRegs = R Nothing Nothing _ srcs
makeEdges {closeDec = NoClose} (Condjmp $ ConditionAny regIdx pp c neg) srcs finalRegs =
  let src : ?; src = Src finalRegs (Just $ CD regIdx pp c neg) in R (Just src) (Just src)  _ srcs
makeEdges {closeDec = (DoClose $ L savedRegs savedSrcs savedUc gs initRegs)} (Condjmp $ ConditionVar regIdx pp c neg) srcs finalRegs =
  R Nothing Nothing _ (Src finalRegs Nothing :: srcs)
makeEdges _ _ _ = trace "Unreachable makeEdges" $ R Nothing Nothing _ []

