module Gens.Auto.Interface.Program


import public Gens.Auto.Interface.Common
import public Spec.Program


public export
genProgram : Fuel ->
             -- Spec.Misc gens
             (Fuel -> Gen MaybeEmpty $ (a ** b ** c ** BoolAnd a b c)) =>
             (Fuel -> (a : _) -> Gen MaybeEmpty $ (b ** c ** BoolAnd a b c)) =>
             (Fuel -> (b : _) -> Gen MaybeEmpty $ (a ** c ** BoolAnd a b c)) =>
             (Fuel -> (c : _) -> Gen MaybeEmpty $ (a ** b ** BoolAnd a b c)) =>
             (Fuel -> (a, b : _) -> Gen MaybeEmpty $ NotSame a b) =>
             -- Spec.Value gens
             (Fuel -> (a : _) -> Gen MaybeEmpty $ RawValue a) =>
             (Fuel -> Gen MaybeEmpty $ (a ** RawValue a)) =>
             (Fuel -> (a : _) -> (b : _) -> Gen MaybeEmpty $ VExpr a b) =>
             (Fuel -> (a : _) -> Gen MaybeEmpty $ (b ** VExpr a b)) =>
             (Fuel -> Gen MaybeEmpty $ (a ** b ** VExpr a b)) =>
             (Fuel -> Gen MaybeEmpty Value) =>
             {n : Nat} -> (ctx : Context n) -> Gen MaybeEmpty (Program ctx)

