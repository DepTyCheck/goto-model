module Spec.Program.Loop.Variant

import public Spec.Context.Loop.Misc
import public Spec.Program.Loop.Decision.Close
import public Spec.Program.ControlFlow.Decision.Edge

%default total

namespace NoClose
  public export
  data HasVariant : (finalRegs : VectValue n) -> Type where
    Here : HasVariant ((JustV {isDet = False} vExpr) :: finalRegs)
    There : HasVariant finalRegs -> HasVariant (fr :: finalRegs)

public export
getVType : {finalRegs : _} -> HasVariant finalRegs -> VType
getVType {finalRegs = (JustV {vTy} {isDet = False} vExpr :: finalRegs)} Here = vTy
getVType (There prf') = getVType prf'

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

namespace DoClose
  public export
  data HasLoopVariant : {0 closeDec : CloseLoopDecision remSrcs ols} ->
                        (initRegs : VectValue n) ->
                        (areWinded' : AreWinded' savedRegs gs initRegs uc initUc) ->
                        (finalRegs : VectValue n) ->
                        (canUnwindAll : CanUnwindAll initRegs gs finalRegs) ->
                        (edgeDec : EdgeDecision closeDec) ->
                        Type where
    Here : {0 closeDec : CloseLoopDecision remSrcs ols} ->
           {0 areWinded'' : AreWinded' savedRegs gs initRegs uc initUc} ->
           {0 edgeDec : EdgeDecision closeDec} ->
           IsMonotonic fr =>
           So (isUndetIDependsOnlyOnSelf ir @{isWinded'} fr) =>
--         HasDependingSourceIfCondjmp (getIndex fr) remSrcs edgeDec =>
           HasLoopVariant {closeDec} (ir :: initRegs)
                          (AreWindedStep' @{isWinded'} areWinded'')
                          (fr :: finalRegs)
                          (CanUnwindAllStep @{canUnwind} canUnwindAll')
                          edgeDec
    There : HasLoopVariant initRegs
                           areWinded''
                           finalRegs
                           canUnwindAll'
                           edgeDec ->
            HasLoopVariant (ir :: initRegs)
                           (AreWindedStep' @{isWinded'} areWinded'')
                           (fr :: finalRegs)
                           (CanUnwindAllStep @{canUnwind} canUnwindAll')
                           edgeDec

public export
data VariantDecision : (closeDec : CloseLoopDecision {n} remSrcs ols) ->
                       (finalRegs : VectValue n) -> 
                       (edgeDec : EdgeDecision closeDec) ->
                       Type where
  NoVariant : NotCondjmp edgeDec =>
              VariantDecision NoClose finalRegs edgeDec
  VariantNoCloseCondjmp : {0 remSrcs : VectSource l n} ->
                          {0 ols : ListLoop n} ->
                          HasVariant finalRegs =>
                          VariantDecision {remSrcs} {ols} NoClose finalRegs Condjmp
  VariantDoClose : HasLoopVariant {closeDec = DoClose ?} initRegs areWinded' finalRegs canUnwindAll edgeDec =>
                   VariantDecision (DoClose $ L savedRegs savedSrcs savedUc gs initRegs @{TheyAreWinded @{areWinded'}}) finalRegs edgeDec
