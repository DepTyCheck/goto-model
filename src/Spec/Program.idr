module Spec.Program

import public Spec.Context

%default total

namespace LinearBlock
  public export
  data LinearBlock : VectValue n -> VectValue n -> Type where
    Assign : (target, i : Fin n) ->
             NotSame target i =>
             LinearBlock (duplicate target i regs) finalRegs ->
             LinearBlock regs finalRegs
    RegOp : (vop : ValueOp) -> (target : Fin n) ->
            Produce vop regs v =>
            LinearBlock (replaceAt target v regs) finalRegs ->
            LinearBlock regs finalRegs
    Finish : LinearBlock regs regs

namespace Possible
  public export
  data IsUndet : Fin n -> VectValue n -> Type where
    Here : IsUndet 0 (JustV {vTy} {isDet=False} _ :: vs)
    There : IsUndet idx' vs -> IsUndet (FS idx') (v :: vs)

  public export
  anyUndetDependsOnlyOnSelf : (initRegs : VectValue n) -> AreWinded' savedRegs gs initRegs uc =>
                              (finalRegs : VectValue n) -> CanUnwindAll initRegs gs finalRegs => Bool
  anyUndetDependsOnlyOnSelf [] @{AreWindedBase'} [] @{CanUnwindAllBase} = False
  anyUndetDependsOnlyOnSelf ((JustV $ Undet vTy uc) :: initRegs) @{AreWindedStep' @{IsWindedGValue' @{IsWindedUndet'}} areWinded''}
                            ((JustV $ Undet vTy uc) :: finalRegs) @{CanUnwindAllStep @{CanUnwindGValue} _} = True
  anyUndetDependsOnlyOnSelf ((JustV vExpr) :: initRegs) @{AreWindedStep' @{IsWindedGValue' @{IsWindedDet'}} areWinded''}
                            ((JustV vExpr) :: finalRegs) @{CanUnwindAllStep @{CanUnwindGValue} _} =
    anyUndetDependsOnlyOnSelf initRegs @{areWinded''} finalRegs
  anyUndetDependsOnlyOnSelf ((JustV $ Undet vTy initIdx) :: initRegs) @{AreWindedStep' @{IsWindedGType'} areWinded''}
                            ((JustV {isDet = finalIsDet} finalExpr) :: finalRegs) @{CanUnwindAllStep @{CanUnwindGType} _} = do
    let b : Bool; b = case finalIsDet of
                           True => False
                           False => dependsOnlyOn initIdx finalExpr
    b || anyUndetDependsOnlyOnSelf initRegs @{areWinded''} finalRegs
  anyUndetDependsOnlyOnSelf (Unkwn :: initRegs) @{AreWindedStep' @{IsWindedGNothing'} areWinded''}
                            (fr :: finalRegs) @{CanUnwindAllStep @{CanUnwindGNothing} _} =
    anyUndetDependsOnlyOnSelf initRegs @{areWinded''} finalRegs
  anyUndetDependsOnlyOnSelf _ _ = False  -- TODO: compiler is broken :(

  public export
  data Sink : (immSrc : MaybeSource n) -> (srcs : VectSource m n) -> (uc : Nat) -> (ols : ListLoop n) ->
              (bs : VectBool m) ->
              {-merged-}Source n -> {l : _} -> {-remained srcs-}VectSource l n -> {-contUc-}Nat -> {-contOls'-}ListLoop n -> Type where
    SinkWithImmediate : {m, n : _} ->
                        {src : Source n} -> {srcs : VectSource m n} -> {uc : _} -> {ols : ListLoop n} ->
                        {bs : VectBool m} ->
                        let extr : ((k ** VectSource k n), (l ** VectSource l n)); extr = extractAtMany' bs srcs in
                        let merged : (Source n, Nat); merged = merge @{ItIsSucc} (src :: (snd $ fst extr)) uc in
                        Sink {m} (Just $ src) srcs uc ols bs (fst merged) (snd $ snd extr) (snd merged) ols
    SinkWithNothing : {m', n : _} ->
                      {src : Source n} -> {srcs : VectSource m' n} -> {uc : _} -> {ols : ListLoop n} ->
                      {bs : VectBool $ S m'} ->
                      (hasTrue : HasTrue bs) =>
                      let extr : ((k' ** VectSource (S k') n), (l ** VectSource l n)); extr = extractAtMany bs (src :: srcs) in
                      let merged : (Source n, Nat); merged = merge @{ItIsSucc} (snd $ fst extr) uc in
                      Sink {m = S m'} Nothing (src :: srcs) uc ols bs (fst merged) (snd $ snd extr) (snd merged) ols

  public export
  data Possible : (remSrcs : VectSource l n) -> (ols : ListLoop n) -> (finalRegs : VectValue n) ->
                  MaybeSource n -> MaybeSource n -> VectSource r n -> ListLoop n -> Type where
    ItIsPossibleToExit : Possible srcs ols regs Nothing Nothing srcs ols
    ItIsPossibleToJmp : Possible srcs ols regs Nothing Nothing (Src regs :: srcs) ols
    ItIsPossibleToCondjmp : IsUndet i regs => Possible srcs ols regs (Just $ Src regs) (Just $ Src regs) srcs ols


-- immediate source - is always taken
-- delayed source - is always avoided for 1 step
-- immediate source is useful because I'll be able to control loops later
-- another reason is that I wish to guarantee 1 further block doesn't get 2 edges from a block before
-- thus, with immediate source I also need a delayed one
-- just delayed isn't enough because it doesn't force the generator to choose the other source
public export
data Program : (immSrc : MaybeSource n) -> (delaSrc : MaybeSource n) -> (srcs : VectSource m n) -> (uc : Nat) -> (ols : ListLoop n) -> Type where
  Step : {srcs : VectSource m n} ->
         {l : _} -> {remSrcs : VectSource l n} -> {contImmSrc, contDelaSrc : _} -> {r : _} -> {contSrcs' : VectSource r n} ->
         (bs : VectBool m) ->
         Sink immSrc srcs uc ols bs curSrc remSrcs contUc contOls' =>
         LinearBlock curSrc.registers finalRegs ->
         Possible remSrcs contOls' finalRegs contImmSrc contDelaSrc contSrcs' contOls =>
         Program contImmSrc contDelaSrc (snd $ append' delaSrc contSrcs') contUc contOls ->
         Program immSrc delaSrc srcs uc ols
  Finish : Program Nothing Nothing [] uc []
  FinishAll : HasOneSource immSrc srcs => Program immSrc Nothing srcs uc []

test : Program {n=2} (Just $ Src [JustV $ Undet I 0, JustV $ Det $ RawI 1]) Nothing [] 0 []
test = Step [] @{SinkWithImmediate} (Assign 0 1 $ Finish) Finish

test1 : Program {n=3} (Just $ Src [JustV $ Undet I 0, JustV $ Undet I 1, JustV $ Det $ RawI 1]) Nothing [] 0 []
test1 = Step [] @{SinkWithImmediate} (Assign 0 1 $ Finish) Finish

