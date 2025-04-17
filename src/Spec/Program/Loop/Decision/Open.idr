module Spec.Program.Loop.Decision.Open

import public Spec.Context.Loop.Misc

%default total

public export
  data OpenLoopDecision : (src : Source n) -> (ols : ListLoop n) -> {-loop filter-}Bool -> Type where
    NoNewLoop : OpenLoopDecision src ols b
    OneNewLoop : {gs : _} -> {initRegs : _} -> {initUc : _}
              -> So ((has GType gs) && (has GNothing gs) && (count GValue gs <= 2))
              => AreWinded src.registers gs initRegs initUc
              => OpenLoopDecision src [] True

