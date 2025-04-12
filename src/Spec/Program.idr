module Spec.Program

import public Spec.Program.Sink
import public Spec.Program.Loop
import public Spec.Program.LinearBlock
import public Spec.Program.Edges

%default total

-- immediate source - is always taken
-- delayed source - is always avoided for 1 step
-- immediate source is useful because I'll be able to control loops later
-- another reason is that I wish to guarantee 1 further block doesn't get 2 edges from a block before
-- thus, with immediate source I also need a delayed one
-- just delayed isn't enough because it doesn't force the generator to choose the other source
public export
data Program : (immSrc : MaybeSource n) -> (delaSrc : MaybeSource n) -> (srcs : VectSource m n)
            -> (cLim : Nat)   -- complexity limit of expressions
            -> (uc : Nat)     -- count of undetermined Values, i.e. (JustV $ Undet ...)
            -> (ols : ListLoop n) -> Type where
  Step : {n : _} -> {0 m : _}
      -> {immSrc, delaSrc : _} -> {srcs : VectSource m n}
      -> {cLim : _}
      -> {uc : _}
      -> {ols : _}
      -> {finalRegs' : _}
      -> (bs : VectBool m)
      -> (sinkPrf : SinkIsValid immSrc srcs bs)
      => let sinkR : ?; sinkR = sink immSrc srcs uc bs @{sinkPrf} in
         let remSrcs' : ?; remSrcs' = snd $ append' delaSrc sinkR.remainedSrcs in
         (loopDec : LoopDecision sinkR.mergedSrc ols)
      => let windR : ?; windR = startLoops sinkR.mergedSrc remSrcs' sinkR.mergedUc ols @{loopDec} in
         (linBlk : LinearBlock cLim windR.currentSrc.registers finalRegs')
      -> So (isSuitable finalRegs' windR.currentOls)
      => (closeDec : CloseLoopDecision windR.remainedSrcs finalRegs' windR.currentOls)
      => let unwindR : ?; unwindR = unwindContext windR.remainedSrcs finalRegs' windR.currentUc windR.currentOls closeDec in
         (edgeDec : EdgeDecision $ getLoopState windR.currentOls closeDec)
      -> let edgesR : ?; edgesR = makeEdges edgeDec unwindR.contSrcs' unwindR.finalRegs in
         Program edgesR.contImmSrc edgesR.contDelaSrc edgesR.contSrcs cLim unwindR.contUc unwindR.contOls
      -> Program immSrc delaSrc srcs cLim uc ols
  Finish : Program Nothing Nothing [] cLim uc []
  FinishAll : HasOneSource immSrc srcs => Program immSrc Nothing srcs cLim uc ols

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
