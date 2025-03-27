module Spec.Program.Labelled

import public Spec.Program

import Data.Vect

%default total

public export
blkCount : Program immSrc delaSrc srcs -> Nat
blkCount (Step a b cont) = S (blkCount cont)
blkCount Finish = Z
blkCount FinishAll = Z  -- TODO: maybe S Z

public export
labelProgram : (prog : Program immSrc delaSrc srcs) -> Vect (blkCount prog) String
labelProgram (Step bs linBlk cont) = do
  let contLbls = labelProgram cont
  "label_\{show $ blkCount cont}" :: contLbls
labelProgram Finish = []
labelProgram FinishAll = []

