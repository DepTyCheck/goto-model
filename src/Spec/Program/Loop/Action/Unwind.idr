module Spec.Program.Loop.Action.Unwind

import public Spec.Program.LinearBlock

%default total

public export
record Result (n : Nat) where
  constructor R
  contSrcsLen' : Nat
  contSrcs' : VectSource contSrcsLen' n
  finalRegs : VectValue n
  contUc : Nat
  contOls : ListLoop n

public export
unwindContext : {n : _}
             -> {l : _}
             -> (remSrcs : VectSource l n)
             -> (finalRegs' : VectValue n)
             -> (curUc : Nat)
             -> (curOls : ListLoop n)
             -> (closeDec : CloseLoopDecision remSrcs curOls)
             -> CanFinish closeDec finalRegs'
             => Result n
unwindContext remSrcs finalRegs' curUc curOls NoClose @{CanSimplyFinish} =
  R _ remSrcs finalRegs' curUc curOls
unwindContext [] finalRegs' curUc (L savedRegs savedSrcs savedUc gs initRegs :: ols)
              (DoClose $ L savedRegs savedSrcs savedUc gs initRegs) @{MustFinishLoop} = do
  let rec : ?; rec = unwind savedRegs savedUc gs initRegs finalRegs'
  R _ savedSrcs (fst rec) (snd rec) ols

