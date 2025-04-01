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

namespace Bool
  namespace Maybe
    public export
    data MaybeBool : Type where
      Nothing : MaybeBool
      Just : Bool -> MaybeBool
  
    public export
    data NotJustFalse : MaybeBool -> Type where
      ItIsJustTrue : NotJustFalse (Just True)
      ItIsNothing : NotJustFalse Nothing

namespace Possible
  public export
  data IsUndet : Fin n -> VectValue n -> Type where
    Here : IsUndet 0 (JustV {vTy} {isDet=False} _ :: vs)
    There : IsUndet idx' vs -> IsUndet (FS idx') (v :: vs)

  public export
  hasUndet : VectValue n -> Bool
  hasUndet [] = False
  hasUndet (Unkwn :: vs) = hasUndet vs
  hasUndet ((JustV {isDet = False} vExpr) :: vs) = True
  hasUndet ((JustV {isDet = True} vExpr) :: vs) = hasUndet vs

  public export
  hasUndetDependsOnlyOnSelf' : (initRegs : VectValue n) -> AreWinded' savedRegs gs initRegs uc initUc =>
                              (finalRegs : VectValue n) -> CanUnwindAll initRegs gs finalRegs => Bool
  hasUndetDependsOnlyOnSelf' [] @{AreWindedBase'} [] @{CanUnwindAllBase} = False
  hasUndetDependsOnlyOnSelf' ((JustV $ Undet vTy uc) :: initRegs) @{AreWindedStep' @{IsWindedGValue' @{IsWindedUndet'}} areWinded''}
                            ((JustV $ Undet vTy uc) :: finalRegs) @{CanUnwindAllStep @{CanUnwindGValue} _} = True
  hasUndetDependsOnlyOnSelf' ((JustV vExpr) :: initRegs) @{AreWindedStep' @{IsWindedGValue' @{IsWindedDet'}} areWinded''}
                            ((JustV vExpr) :: finalRegs) @{CanUnwindAllStep @{CanUnwindGValue} _} =
    hasUndetDependsOnlyOnSelf' initRegs @{areWinded''} finalRegs
  hasUndetDependsOnlyOnSelf' ((JustV $ Undet vTy initIdx) :: initRegs) @{AreWindedStep' @{IsWindedGType'} areWinded''}
                            ((JustV {isDet = finalIsDet} finalExpr) :: finalRegs) @{CanUnwindAllStep @{CanUnwindGType} _} = do
    let b : Bool; b = case finalIsDet of
                           True => False
                           False => dependsOnlyOn initIdx finalExpr
    b || hasUndetDependsOnlyOnSelf' initRegs @{areWinded''} finalRegs
  hasUndetDependsOnlyOnSelf' (Unkwn :: initRegs) @{AreWindedStep' @{IsWindedGNothing'} areWinded''}
                            (fr :: finalRegs) @{CanUnwindAllStep @{CanUnwindGNothing} _} =
    hasUndetDependsOnlyOnSelf' initRegs @{areWinded''} finalRegs
  hasUndetDependsOnlyOnSelf' _ _ = False  -- TODO: compiler is broken :(

  public export
  hasUndetDependsOnlyOnSelf : (initRegs : VectValue n) -> AreWinded savedRegs gs initRegs initUc =>
                              (finalRegs : VectValue n) -> CanUnwindAll initRegs gs finalRegs => Bool
  hasUndetDependsOnlyOnSelf initRegs @{TheyAreWinded @{areWinded'}} finalRegs @{canUnwindAll} =
    hasUndetDependsOnlyOnSelf' initRegs @{areWinded'} finalRegs @{canUnwindAll}

  public export
  data Sink : (immSrc : MaybeSource n) -> (srcs : VectSource m n) -> (uc : Nat) ->
              (bs : VectBool m) ->
              {-merged-}Source n -> {l : _} -> {-remained srcs-}VectSource l n -> {-contUc-}Nat -> Type where
    SinkWithImmediate : {m, n : _} ->
                        {src : Source n} -> {srcs : VectSource m n} -> {uc : _} ->
                        {bs : VectBool m} ->
                        let extr : ((k ** VectSource k n), (l ** VectSource l n)); extr = extractAtMany' bs srcs in
                        let merged : (Source n, Nat); merged = merge @{ItIsSucc} (src :: (snd $ fst extr)) uc in
                        Sink {m} (Just $ src) srcs uc bs (fst merged) (snd $ snd extr) (snd merged)
    SinkWithNothing : {m', n : _} ->
                      {src : Source n} -> {srcs : VectSource m' n} -> {uc : _} ->
                      {bs : VectBool $ S m'} ->
                      HasTrue bs =>
                      let extr : ((k' ** VectSource (S k') n), (l ** VectSource l n)); extr = extractAtMany bs (src :: srcs) in
                      let merged : (Source n, Nat); merged = merge @{ItIsSucc} (snd $ fst extr) uc in
                      Sink {m = S m'} Nothing (src :: srcs) uc bs (fst merged) (snd $ snd extr) (snd merged)

  public export
  data StartLoops : (src : Source n) -> (remSrcs' : VectSource l n) -> (uc : Nat) -> (ols : ListLoop n) ->
                    {-initSrc-}Source n -> {r : _} -> {-remSrcs-}VectSource r n -> {-initUc-}Nat -> {-newOls-}ListLoop n -> Type where
    [search src remSrcs' uc ols]
    NoNewLoop : StartLoops src remSrcs' uc ols src remSrcs' uc ols
    -- TODO: allow many loops
    OneNewLoop : (areWinded : AreWinded src.registers gs initRegs initUc) =>
                 StartLoops src remSrcs' uc ols (Src initRegs) [] initUc [L src.registers remSrcs' uc gs initRegs @{areWinded}]

  public export
  isSuitable : (finalRegs : VectValue n) -> ListLoop n -> Bool
  isSuitable finalRegs [] = True
  isSuitable finalRegs (ol :: ols) = hasUndet finalRegs

  public export
  data CloseLoopDecision : (remSrcs : VectSource l n) -> (finalRegs : VectValue n) -> (ols : ListLoop n) -> Type where
    NoClose : CloseLoopDecision remSrcs finalRegs ols
    -- TODO: remSrcs may not be [], I just don't want to unwind them now
    DoClose : (canUnwindAll : CanUnwindAll initRegs gs finalRegs) =>
              So (hasUndetDependsOnlyOnSelf initRegs @{areWinded} finalRegs @{canUnwindAll}) =>
              CloseLoopDecision [] finalRegs ((L savedRegs savedSrcs savedUc gs initRegs @{areWinded}) :: ols)

  public export
  unwindContext : {n : Nat} ->
                  {l : Nat} -> (remSrcs : VectSource l n) -> (finalRegs' : VectValue n) -> (curUc : Nat) -> (curOls : ListLoop n) -> CloseLoopDecision remSrcs finalRegs' curOls ->
                  ({-contSrcs'-}(r ** VectSource r n), {-finalRegs-}VectValue n, {-contUc-}Nat, {-contOls-}ListLoop n)
  unwindContext remSrcs finalRegs' curUc curOls NoClose =
    ((_ ** remSrcs), finalRegs', curUc, curOls)
  unwindContext [] finalRegs' _ (L savedRegs savedSrcs savedUc gs initRegs @{areWinded} :: ols) DoClose = do
    let rec : ?; rec = unwind savedRegs savedUc gs initRegs finalRegs' @{areWinded}
    let finalRegs : ?; finalRegs = fst rec
    let contUc : ?; contUc = snd rec
    ((_ ** savedSrcs), finalRegs, contUc, ols)

  public export
  getLoopState : (curOls : ListLoop n) -> CloseLoopDecision remSrcs finalRegs' curOls -> MaybeBool
  getLoopState [] NoClose = Nothing
  getLoopState (_ :: _) NoClose = Just False
  getLoopState (L savedRegs savedSrcs savedUc gs initRegs :: ols) DoClose = Just True

  public export
  data EdgeDecision : {-hasLoop and canEnd = Just True-}MaybeBool -> Type where
    Exit : NotJustFalse loopState => EdgeDecision loopState
    Jmp : EdgeDecision loopState
    Condjmp : EdgeDecision loopState

  %name EdgeDecision edgeDec

  public export
  makeEdges : {mb : _} -> EdgeDecision mb -> {l : _} -> (srcs : VectSource l n) -> (finalRegs : VectValue n) ->
              (MaybeSource n, MaybeSource n, (r ** VectSource r n))
  makeEdges {mb} (Exit @{notJustFalse}) srcs finalRegs = (Nothing, Nothing, (_ ** srcs))
  makeEdges {mb} Jmp srcs finalRegs = do
    case mb of
         (Just True) => (Nothing, Nothing, (_ ** srcs))
         _ => (Nothing, Nothing, (_ ** Src finalRegs :: srcs))
  makeEdges {mb} Condjmp srcs finalRegs = do
    case mb of
         (Just True) => (Nothing, Nothing, (_ ** Src finalRegs :: srcs))
         _ => (Just $ Src finalRegs, Just $ Src finalRegs, (_ ** srcs))

-- immediate source - is always taken
-- delayed source - is always avoided for 1 step
-- immediate source is useful because I'll be able to control loops later
-- another reason is that I wish to guarantee 1 further block doesn't get 2 edges from a block before
-- thus, with immediate source I also need a delayed one
-- just delayed isn't enough because it doesn't force the generator to choose the other source
public export
data Program : (immSrc : MaybeSource n) -> (delaSrc : MaybeSource n) -> (srcs : VectSource m n) ->
               (uc : Nat) ->  -- count of undetermined Values, i.e. (JustV $ Undet ...)
               (ols : ListLoop n) -> Type where
  Step : {n : _} -> {0 m : _} ->
         {immSrc, delaSrc : _} -> {srcs : VectSource m n} ->
         {0 uc : _} ->
         {0 ols : _} ->
         {0 mergedSrc : _} -> {l : _} -> {remSrcs'' : VectSource l n} -> {0 mergedUc : _} ->
         {0 curSrc : _} -> {r : _} -> {remSrcs : VectSource r n} -> {curUc : _} -> {curOls : _} ->
         {finalRegs' : _} ->
         (bs : VectBool m) ->
         Sink immSrc srcs uc bs mergedSrc remSrcs'' mergedUc =>
         let remSrcs' : ?; remSrcs' = snd $ append' delaSrc remSrcs'' in
         StartLoops mergedSrc remSrcs' mergedUc ols curSrc remSrcs curUc curOls =>
         (linBlk : LinearBlock curSrc.registers finalRegs') ->
         So (isSuitable finalRegs' curOls) =>
         (closeDec : CloseLoopDecision remSrcs finalRegs' curOls) =>
         let unwindedCtx : ?; unwindedCtx = unwindContext remSrcs finalRegs' curUc curOls closeDec in 
         let contSrcs' : ?; contSrcs' = snd $ fst unwindedCtx in
         let finalRegs : ?; finalRegs = fst $ snd unwindedCtx in
         let contUc : ?; contUc = fst $ snd $ snd unwindedCtx in
         let contOls : ?; contOls = snd $ snd $ snd unwindedCtx in
         (edgeDec : EdgeDecision $ getLoopState curOls closeDec) ->
         let edges : ?; edges = makeEdges edgeDec contSrcs' finalRegs in
         let contImmSrc : ?; contImmSrc = fst edges in
         let contDelaSrc : ?; contDelaSrc = fst $ snd edges in
         let contSrcs : ?; contSrcs = snd $ snd $ snd edges in
         Program contImmSrc contDelaSrc contSrcs contUc contOls ->
         Program immSrc delaSrc srcs uc ols
  Finish : Program Nothing Nothing [] uc []
  FinishAll : HasOneSource immSrc srcs => Program immSrc Nothing srcs uc []

test : Program {n=2} (Just $ Src [JustV $ Undet I 0, JustV $ Det $ RawI 1]) Nothing [] 1 []
test = Step [] @{SinkWithImmediate} @{NoNewLoop} (Assign 0 1 $ Finish) @{Oh} Exit @{NoClose} $ Finish

test1 : Program {n=3} (Just $ Src [JustV $ Undet I 0, JustV $ Undet I 1, JustV $ Det $ RawI 1]) Nothing [] 0 []
test1 = Step [] @{SinkWithImmediate} @{NoNewLoop} (Assign 0 1 $ Finish) @{Oh} Exit @{NoClose} Finish

test2 : Program {n=3} (Just $ Src [JustV $ Undet I 0, JustV $ Undet I 1, JustV $ Det $ RawI 1]) Nothing [] 2 []
test2 = Step [] @{SinkWithImmediate} @{OneNewLoop {gs=[GType, GType, GValue]} @{TheyAreWinded @{AreWindedStep' $ AreWindedStep' @{IsWindedGType'} $ AreWindedStep' @{IsWindedGValue'} $ AreWindedBase'}}} (
          Assign 1 0 $
          RegOp Add 0 @{ProduceOp @{HasTypeHere} @{ItIsAddVTypes} @{HasTypeThere $ HasTypeThere $ HasTypeHere}} $
          Finish
          ) @{Oh} (Exit) @{DoClose} Finish
