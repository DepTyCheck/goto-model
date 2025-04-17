module Spec.Program.Loop.Action.Wind

import public Spec.Program.Loop.Decision.Open

public export
record Result (n : Nat) where
  constructor R
  currentSrc : Source n
  remainedSrcsLen : Nat
  remainedSrcs : VectSource remainedSrcsLen n
  currentUc : Nat
  currentOls : ListLoop n

public export
windContext : (src : Source n)
           -> {l : _}
           -> (remSrcs' : VectSource l n)
           -> (uc : Nat)
           -> (ols : ListLoop n)
           -> (openDec : OpenLoopDecision src ols b)
           => Result n
windContext src remSrcs' uc ols @{NoNewLoop} = R src _ remSrcs' uc ols
windContext src remSrcs' uc [] @{OneNewLoop {gs} {initRegs} {initUc}} = R (Src initRegs) _ [] initUc [L src.registers remSrcs' uc gs initRegs]

