module Spec.Program.Loop.Decision.Close

import public Spec.Context.Loop

%default total

public export
data CloseLoopDecision : (remSrcs : VectSource l n) -> (ols : ListLoop n) -> Type where
  NoClose : CloseLoopDecision remSrcs ols
  -- TODO: remSrcs may not be [], I just don't want to unwind them now
  DoClose : (ol : Loop n) -> CloseLoopDecision [] (ol :: ols)

