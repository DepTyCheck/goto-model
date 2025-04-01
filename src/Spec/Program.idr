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
    [search immSrc srcs uc bs]
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
    NoNewLoop : StartLoops src remSrcs' uc ols src remSrcs' uc ols
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
  data ErasedVectSource : Nat -> Type where
    EVS : (l : Nat) -> VectSource l n -> ErasedVectSource n

  public export
  (.length) : ErasedVectSource n -> Nat
  (.length) (EVS l srcs) = l

  public export
  (.sources) : (erasedSrcs : ErasedVectSource n) -> VectSource (erasedSrcs.length) n
  (.sources) (EVS l srcs) = srcs

  public export
  unwindContext : {n : Nat} ->
                  {l : Nat} -> (remSrcs : VectSource l n) -> (finalRegs' : VectValue n) -> (curUc : Nat) -> (curOls : ListLoop n) -> CloseLoopDecision remSrcs finalRegs' curOls ->
                  ({-contSrcs'-}ErasedVectSource n, {-finalRegs-}VectValue n, {-contUc-}Nat, {-contOls-}ListLoop n)
  unwindContext remSrcs finalRegs' curUc curOls NoClose =
    (EVS _ remSrcs, finalRegs', curUc, curOls)
  unwindContext [] finalRegs' _ (L savedRegs savedSrcs savedUc gs initRegs @{areWinded} :: ols) DoClose = do
    let rec : ?; rec = unwind savedRegs savedUc gs initRegs finalRegs' @{areWinded}
    let finalRegs : ?; finalRegs = fst rec
    let contUc : ?; contUc = snd rec
    (EVS _ savedSrcs, finalRegs, contUc, ols)

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
              (MaybeSource n, MaybeSource n, ErasedVectSource n)
  makeEdges {mb} (Exit @{notJustFalse}) srcs finalRegs = (Nothing, Nothing, EVS _ srcs)
  makeEdges {mb} Jmp srcs finalRegs = do
    case mb of
         (Just True) => (Nothing, Nothing, EVS _ srcs)
         _ => (Nothing, Nothing, EVS _ $ Src finalRegs :: srcs)
  makeEdges {mb} Condjmp srcs finalRegs = do
    case mb of
         (Just True) => (Nothing, Nothing, EVS _ $ Src finalRegs :: srcs)
         _ => (Just $ Src finalRegs, Just $ Src finalRegs, EVS _ srcs)

  public export
  makeEdges' : {mb : _} -> EdgeDecision mb -> {l : _} -> (srcs : VectSource l n) -> (finalRegs : VectValue n) ->
               (ErasedVectSource n, MaybeSource n, MaybeSource n)
  makeEdges' {mb} Exit srcs finalRegs = (EVS _ srcs, Nothing, Nothing)
  makeEdges' {mb = Just True} Jmp srcs finalRegs = (EVS _ srcs, Nothing, Nothing)
  makeEdges' {mb = _} Jmp srcs finalRegs = (EVS _ (Src finalRegs :: srcs), Nothing, Nothing)
  makeEdges' {mb = Just True} Condjmp srcs finalRegs = (EVS _ (Src finalRegs :: srcs), Nothing, Nothing)
  makeEdges' {mb = _} Condjmp srcs finalRegs = (EVS _ srcs, Just $ Src finalRegs, Just $ Src finalRegs)


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
  Step : {n : _} -> {m : _} ->
         {immSrc, delaSrc : _} -> {srcs : VectSource m n} ->
         {uc : _} ->
         {ols : _} ->
         {mergedSrc : _} -> {l : _} -> {remSrcs'' : VectSource l n} ->
         {curSrc : _} -> {r : _} -> {remSrcs : VectSource r n} -> {curUc : _} -> {curOls : _} ->
         {finalRegs' : _} ->
         (bs : VectBool m) ->
         Sink immSrc srcs uc bs mergedSrc remSrcs'' mergedUc =>
         StartLoops mergedSrc (snd $ append' delaSrc remSrcs'') mergedUc ols curSrc remSrcs curUc curOls =>
         (linBlk : LinearBlock curSrc.registers finalRegs') ->
         So (isSuitable finalRegs' curOls) =>
         (closeDec : CloseLoopDecision remSrcs finalRegs' curOls) =>
         let unwindedCtx : (ErasedVectSource n, VectValue n, Nat, ListLoop n); unwindedCtx = unwindContext {n=n} {l=r} remSrcs finalRegs' curUc curOls closeDec in
         let loopState : ?; loopState = getLoopState curOls closeDec in
         (edgeDec : EdgeDecision loopState) ->
         let edges : ?; contCtx = makeEdges' {n=n} edgeDec {l=(fst unwindedCtx).length} (fst unwindedCtx).sources (fst $ snd unwindedCtx) in
             {-
         Program (fst $ snd edges) (snd $ snd edges) (fst edges).sources (fst $ snd $ snd unwindedCtx) (snd $ snd $ snd unwindedCtx) ->
         -}
         Program immSrc delaSrc srcs uc ols
  Finish : Program Nothing Nothing [] uc []
  FinishAll : HasOneSource immSrc srcs => Program immSrc Nothing srcs uc []

test_immSrc : MaybeSource 2
test_immSrc = (Just $ Src [JustV $ Undet I 0, JustV $ Det $ RawI 1])

test_sink : Sink Program.test_immSrc [] 1 [] (Src [JustV $ Undet I 0, JustV $ Det $ RawI 1]) [] 1
test_sink = SinkWithImmediate

test_loops : StartLoops (Src [JustV $ Undet I 0, JustV $ Det $ RawI 1]) (snd $ append' Nothing []) 1 [] (Src [JustV $ Undet I 0, JustV $ Det $ RawI 1]) [] 1 []
test_loops = NoNewLoop

test_closeDec : CloseLoopDecision [] [JustV $ Det $ RawI 1, JustV $ Det $ RawI 1] []
test_closeDec = NoClose

test_unwindedCtx : ?
test_unwindedCtx = unwindContext [] [JustV $ Det $ RawI 1, JustV $ Det $ RawI 1] 1 [] Program.test_closeDec

test_edgeDec : EdgeDecision $ getLoopState [] Program.test_closeDec
test_edgeDec = Exit

test_edges : (MaybeSource 2, MaybeSource 2, ErasedVectSource 2)
test_edges = makeEdges test_edgeDec (fst test_unwindedCtx).sources (fst $ snd test_unwindedCtx)

test : Program {n=2} (Just $ Src [JustV $ Undet I 0, JustV $ Det $ RawI 1]) Nothing [] 1 []
test = Step [] @{SinkWithImmediate} @{NoNewLoop} (Assign 0 1 $ Finish) @{Oh} @{NoClose} Exit -- $ Finish

{-
test1 : Program {n=3} (Just $ Src [JustV $ Undet I 0, JustV $ Undet I 1, JustV $ Det $ RawI 1]) Nothing [] 0 []
test1 = Step [] @{SinkWithImmediate} (Assign 0 1 $ Finish) @{ItIsPossibleToExit} Finish

