module Spec.Program.Loop

import public Spec.Context.Loop

%default total

namespace Wind
  public export
  data LoopDecision : (src : Source n) -> (ols : ListLoop n) -> Type where
    NoNewLoop : LoopDecision src ols
    OneNewLoop : {gs : _} -> {initRegs : _} -> {initUc : _}
              -> AreWinded src.registers gs initRegs initUc
              => LoopDecision src []
  
  public export
  record Result (n : Nat) where
    constructor R
    currentSrc : Source n
    remainedSrcsLen : Nat
    remainedSrcs : VectSource remainedSrcsLen n
    currentUc : Nat
    currentOls : ListLoop n
  
  public export
  startLoops : (src : Source n) -> {l : _} -> (remSrcs' : VectSource l n) -> (uc : Nat) -> (ols : ListLoop n) -> (loopDec : LoopDecision src ols)
            => Result n
  startLoops src remSrcs' uc ols @{NoNewLoop} = R src _ remSrcs' uc ols
  startLoops src remSrcs' uc [] @{OneNewLoop {gs} {initRegs} {initUc}} = R (Src initRegs) _ [] initUc [L src.registers remSrcs' uc gs initRegs]

namespace Unwind
  public export
  data CloseLoopDecision : (remSrcs : VectSource l n) -> (finalRegs : VectValue n) -> (ols : ListLoop n) -> Type where
    NoClose : CloseLoopDecision remSrcs finalRegs ols
    -- TODO: remSrcs may not be [], I just don't want to unwind them now
    DoClose : (canUnwindAll : CanUnwindAll initRegs gs finalRegs) =>
              -- TODO: not enough, need to check for a particular expression
              So (hasUndetDependsOnlyOnSelf initRegs @{areWinded} finalRegs @{canUnwindAll}) =>
  
              CloseLoopDecision [] finalRegs ((L savedRegs savedSrcs savedUc gs initRegs @{areWinded}) :: ols)
  
  public export
  record Result (n : Nat) where
    constructor R
    contSrcsLen' : Nat
    contSrcs' : VectSource contSrcsLen' n
    finalRegs : VectValue n
    contUc : Nat
    contOls : ListLoop n
  
  public export
  unwindContext : {n : Nat}
               -> {l : Nat} -> (remSrcs : VectSource l n) -> (finalRegs' : VectValue n) -> (curUc : Nat) -> (curOls : ListLoop n) -> CloseLoopDecision remSrcs finalRegs' curOls
               -> Unwind.Result n
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
