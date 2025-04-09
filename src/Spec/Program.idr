module Spec.Program

import public Spec.Context

%default total

namespace LinearBlock
  public export
  data LinearBlock : (cLim : Nat) -> (regs : VectValue n) -> VectValue n -> Type where
    Assign : (target, i : Fin n) ->
             NotSame target i =>
             LinearBlock cLim (duplicate target i regs) finalRegs ->
             LinearBlock cLim regs finalRegs
    RegOp : (vop : ValueOp) -> (target : Fin n) ->
            Produce vop cLim regs v =>
            LinearBlock cLim (replaceAt target v regs) finalRegs ->
            LinearBlock cLim regs finalRegs
    Finish : LinearBlock cLim regs regs

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

namespace Step
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
  data SinkIsValid : (immSrc : MaybeSource n) -> (srcs : VectSource m n) -> (bs : VectBool m) -> Type where
    SinkIsValidWithImmediate : SinkIsValid (Just src) srcs bs
    SinkIsValidWithNothing : HasTrue bs => SinkIsValid Nothing (src :: srcs) bs

  namespace Sink
    public export
    record Result (n : Nat) where
      constructor R
      mergedSrc : Source n
      remainedSrcsLen : Nat
      remainedSrcs : VectSource remainedSrcsLen n
      mergedUc : Nat

  public export
  sink : {n : _} -> (immSrc : MaybeSource n) -> (srcs : VectSource m n) -> (uc : Nat) -> (bs : VectBool m) -> SinkIsValid immSrc srcs bs =>
         Sink.Result n
  sink (Just src) srcs uc bs @{SinkIsValidWithImmediate} = do
    let extr : ?; extr = extractAtMany' bs srcs
    let merged : ?; merged = merge (src :: (snd $ fst extr)) uc
    R (fst merged) _ (snd $ snd extr) (snd merged)
  sink Nothing (src :: srcs) uc bs @{SinkIsValidWithNothing} = do
    let extr : ?; extr = extractAtMany bs (src :: srcs)
    let merged : ?; merged = merge (snd $ fst extr) uc
    R (fst merged) _ (snd $ snd extr) (snd merged)

  public export
  data LoopDecision : (src : Source n) -> (ols : ListLoop n) -> Type where
    NoNewLoop : LoopDecision src ols
    OneNewLoop : {gs : _} -> {initRegs : _} -> {initUc : _} ->
                 AreWinded src.registers gs initRegs initUc =>
                 LoopDecision src []

  namespace Wind
    public export
    record Result (n : Nat) where
      constructor R
      currentSrc : Source n
      remainedSrcsLen : Nat
      remainedSrcs : VectSource remainedSrcsLen n
      currentUc : Nat
      currentOls : ListLoop n

  public export
  startLoops : (src : Source n) -> {l : _} -> (remSrcs' : VectSource l n) -> (uc : Nat) -> (ols : ListLoop n) -> (loopDec : LoopDecision src ols) =>
               Wind.Result n
  startLoops src remSrcs' uc ols @{NoNewLoop} = R src _ remSrcs' uc ols
  startLoops src remSrcs' uc [] @{OneNewLoop {gs} {initRegs} {initUc}} = R (Src initRegs) _ [] initUc [L src.registers remSrcs' uc gs initRegs]

  public export
  isSuitable : (finalRegs : VectValue n) -> ListLoop n -> Bool
  isSuitable finalRegs [] = True
  isSuitable finalRegs (ol :: ols) = hasUndet finalRegs

  public export
  data CloseLoopDecision : (remSrcs : VectSource l n) -> (finalRegs : VectValue n) -> (ols : ListLoop n) -> Type where
    NoClose : CloseLoopDecision remSrcs finalRegs ols
    -- TODO: remSrcs may not be [], I just don't want to unwind them now
    DoClose : (canUnwindAll : CanUnwindAll initRegs gs finalRegs) =>
              -- TODO: not enough, need to check for a particular expression
              So (hasUndetDependsOnlyOnSelf initRegs @{areWinded} finalRegs @{canUnwindAll}) =>

              CloseLoopDecision [] finalRegs ((L savedRegs savedSrcs savedUc gs initRegs @{areWinded}) :: ols)

  namespace Unwind
    public export
    record Result (n : Nat) where
      constructor R
      contSrcsLen' : Nat
      contSrcs' : VectSource contSrcsLen' n
      finalRegs : VectValue n
      contUc : Nat
      contOls : ListLoop n

  public export
  unwindContext : {n : Nat} ->
                  {l : Nat} -> (remSrcs : VectSource l n) -> (finalRegs' : VectValue n) -> (curUc : Nat) -> (curOls : ListLoop n) -> CloseLoopDecision remSrcs finalRegs' curOls ->
                  Unwind.Result n
  unwindContext remSrcs finalRegs' curUc curOls NoClose =
    R _ remSrcs finalRegs' curUc curOls
  unwindContext [] finalRegs' _ (L savedRegs savedSrcs savedUc gs initRegs @{areWinded} :: ols) DoClose = do
    let rec : ?; rec = unwind savedRegs savedUc gs initRegs finalRegs' @{areWinded}
    R _ savedSrcs (fst rec) (snd rec) ols

  public export
  getLoopState : (curOls : ListLoop n) -> CloseLoopDecision remSrcs finalRegs' curOls -> MaybeBool
  getLoopState [] NoClose = Nothing
  getLoopState (_ :: _) NoClose = Just False
  getLoopState (L savedRegs savedSrcs savedUc gs initRegs :: _) DoClose = Just True

  public export
  data EdgeDecision : {-hasLoop and canEnd = Just True-}MaybeBool -> Type where
    Exit : NotJustFalse loopState => EdgeDecision loopState
    Jmp : EdgeDecision loopState
    -- TODO: condjmp is only possible then we can end the loop or there's no loop but 1 undet value
    Condjmp : EdgeDecision loopState

  %name EdgeDecision edgeDec

  namespace Edges
    public export
    record Result (n : Nat) where
      constructor R
      contImmSrc : MaybeSource n
      contDelaSrc : MaybeSource n
      contSrcsLen : Nat
      contSrcs : VectSource contSrcsLen n

  public export
  makeEdges : {mb : _} -> EdgeDecision mb -> {l : _} -> (srcs : VectSource l n) -> (finalRegs : VectValue n) ->
              Edges.Result n
  makeEdges {mb} (Exit @{notJustFalse}) srcs finalRegs = R Nothing Nothing _ srcs
  makeEdges {mb} Jmp srcs finalRegs = do
    case mb of
         (Just True) => R Nothing Nothing _ srcs
         _ => R Nothing Nothing _ (Src finalRegs :: srcs)
  makeEdges {mb} Condjmp srcs finalRegs = do
    case mb of
         (Just True) => R Nothing Nothing _ (Src finalRegs :: srcs)
         _ => R (Just $ Src finalRegs) (Just $ Src finalRegs) _ srcs

-- immediate source - is always taken
-- delayed source - is always avoided for 1 step
-- immediate source is useful because I'll be able to control loops later
-- another reason is that I wish to guarantee 1 further block doesn't get 2 edges from a block before
-- thus, with immediate source I also need a delayed one
-- just delayed isn't enough because it doesn't force the generator to choose the other source
public export
data Program : (immSrc : MaybeSource n) -> (delaSrc : MaybeSource n) -> (srcs : VectSource m n) ->
               (cLim : Nat) ->  -- complexity limit of expressions
               (uc : Nat) ->  -- count of undetermined Values, i.e. (JustV $ Undet ...)
               (ols : ListLoop n) -> Type where
  Step : {n : _} -> {0 m : _} ->
         {immSrc, delaSrc : _} -> {srcs : VectSource m n} ->
         {cLim : _} ->
         {uc : _} ->
         {ols : _} ->
         {finalRegs' : _} ->
         (bs : VectBool m) ->
         (sinkPrf : SinkIsValid immSrc srcs bs) =>
         let sinkR : ?; sinkR = sink immSrc srcs uc bs @{sinkPrf} in
         let remSrcs' : ?; remSrcs' = snd $ append' delaSrc sinkR.remainedSrcs in
         (loopDec : LoopDecision sinkR.mergedSrc ols) =>
         let windR : ?; windR = startLoops sinkR.mergedSrc remSrcs' sinkR.mergedUc ols @{loopDec} in
         (linBlk : LinearBlock cLim windR.currentSrc.registers finalRegs') ->
         So (isSuitable finalRegs' windR.currentOls) =>
         (closeDec : CloseLoopDecision windR.remainedSrcs finalRegs' windR.currentOls) =>
         let unwindR : ?; unwindR = unwindContext windR.remainedSrcs finalRegs' windR.currentUc windR.currentOls closeDec in 
         (edgeDec : EdgeDecision $ getLoopState windR.currentOls closeDec) ->
         let edgesR : ?; edgesR = makeEdges edgeDec unwindR.contSrcs' unwindR.finalRegs in
         Program edgesR.contImmSrc edgesR.contDelaSrc edgesR.contSrcs cLim unwindR.contUc unwindR.contOls ->
         Program immSrc delaSrc srcs cLim uc ols
  Finish : Program Nothing Nothing [] cLim uc []
  FinishAll : HasOneSource immSrc srcs => Program immSrc Nothing srcs cLim uc []

test : Program {n=2} (Just $ Src [JustV $ Undet I 0, JustV $ Det $ RawI 1]) Nothing [] 2 1 []
test = Step [] @{SinkIsValidWithImmediate} @{NoNewLoop} (Assign 0 1 $ Finish) @{Oh} Exit @{NoClose} $ Finish

test1 : Program {n=3} (Just $ Src [JustV $ Undet I 0, JustV $ Undet I 1, JustV $ Det $ RawI 1]) Nothing [] 2 0 []
test1 = Step [] @{SinkIsValidWithImmediate} @{NoNewLoop} (Assign 0 1 $ Finish) @{Oh} Exit @{NoClose} Finish

test2 : Program {n=3} (Just $ Src [JustV $ Undet I 0, JustV $ Undet I 1, JustV $ Det $ RawI 1]) Nothing [] 5 2 []
test2 = Step [] @{SinkIsValidWithImmediate} @{OneNewLoop {gs=[GType, GType, GValue]} @{TheyAreWinded @{AreWindedStep' $ AreWindedStep' @{IsWindedGType'} $ AreWindedStep' @{IsWindedGValue'} $ AreWindedBase'}}} (
          Assign 1 0 $
          RegOp Add 0 @{ProduceOp @{HasTypeHere {ltePrf=LTEZero}} @{ItIsAddVTypes} @{HasTypeThere $ HasTypeThere $ HasTypeHere {ltePrf=LTEZero}}} $
          Finish
          ) @{Oh} (Exit) @{DoClose} Finish
