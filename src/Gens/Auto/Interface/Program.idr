module Gens.Auto.Interface.Program

import public Gens.Auto.Interface.Common
import public Spec.Program
import public Show.Program.Raw
import public Show.Value

public export
genProgram : Fuel ->
             (Fuel -> {m, n : _} -> (a : MaybeSource n) -> (b : VectSource m n) -> Gen MaybeEmpty (c ** SinkIsValid a b c)) =>
             (Fuel -> {n : _} -> (a : Source n) -> (b : ListLoop n) -> Gen MaybeEmpty (LoopDecision a b)) =>
             (Fuel -> {n, l : _} -> (a : VectSource l n) -> (b : VectValue n) -> (c : ListLoop n) -> Gen MaybeEmpty (CloseLoopDecision a b c)) =>
             (Fuel -> {n : _} -> (a : _) -> (b : VectValue n) -> Gen MaybeEmpty (c ** LinearBlock a b c)) =>
             (Fuel -> (a : MaybeBool) -> Gen MaybeEmpty (EdgeDecision a)) =>
             {m, n : Nat} -> (immSrc : MaybeSource n) -> (delaSrc : MaybeSource n) -> (srcs : VectSource m n) -> (cLim : Nat) -> (uc : Nat) -> (ols : ListLoop n) ->
             Gen MaybeEmpty $ Program immSrc delaSrc srcs cLim uc ols

