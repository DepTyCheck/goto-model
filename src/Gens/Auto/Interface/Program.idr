module Gens.Auto.Interface.Program

import public Gens.Auto.Interface.Common
import public Spec.Program

public export
genProgram : Fuel ->
             (Fuel ->
              {m, n : _} ->
              (a : MaybeSource n) ->
              (b : VectSource m n) ->
              Gen MaybeEmpty (c ** SinkIsValid a b c)) =>
             (Fuel ->
              {n : _} ->
              (a : Source n) ->
              (b : ListLoop n) ->
              (c : Bool) ->
              Gen MaybeEmpty $ OpenLoopDecision a b c) =>
             (Fuel ->
              {n, l : _} ->
              (a : VectSource l n) ->
              (b : ListLoop n) ->
              Gen MaybeEmpty $ CloseLoopDecision a b) =>
             (Fuel ->
              {n : _} ->
              (a : _) ->
              {l : _} ->
              {b1 : VectSource l n} ->
              {b2 : ListLoop n} ->
              (b : CloseLoopDecision b1 b2) ->
              (c : VectValue n) ->
              Gen MaybeEmpty (d ** LinearBlock a b c d)) =>
             (Fuel ->
              {n, l : _} ->
              {a2 : _} ->
              {a1 : VectSource l n} ->
              (a : CloseLoopDecision a1 a2) ->
              Gen MaybeEmpty $ EdgeDecision a) =>
             (Fuel ->
              {n, l : _} ->
              {a2 : _} ->
              {a1 : VectSource l n} ->
              (a : CloseLoopDecision a1 a2) ->
              (b : VectValue t) ->
              (c : EdgeDecision a) ->
              Gen MaybeEmpty $ VariantDecision a b c) =>
             (Fuel ->
              {a : CloseLoopDecision a1 a2} ->
              (b : EdgeDecision a) ->
              (c : VariantDecision a d b) ->
              Gen MaybeEmpty $ ConditionDecision b c) =>
             {m, n : Nat} ->
             (immSrc : MaybeSource n) ->
             (delaSrc : MaybeSource n) ->
             (srcs : VectSource m n) ->
             (cLim : Nat) ->
             (uc : Nat) ->
             (ols : ListLoop n) ->
             Gen MaybeEmpty $ Program immSrc delaSrc srcs cLim uc ols

