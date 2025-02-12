module Gens.Auto.Interface.Value


import public Gens.Auto.Interface.Common
import public Spec.Misc
import public Spec.Value


public export
genRawValue0 : Fuel -> (vTy : _) -> Gen MaybeEmpty $ RawValue vTy

public export
genRawValue : Fuel ->
              (Fuel -> (a : _) -> Gen MaybeEmpty $ RawValue a) =>
              Gen MaybeEmpty $ (vTy ** RawValue vTy)

public export
genVExpr01 : Fuel ->
             (Fuel -> (c : _) -> Gen MaybeEmpty $ (a ** b ** BoolAnd a b c)) =>
             (Fuel -> (a : _) -> Gen MaybeEmpty $ RawValue a) =>
             (mVTy : _) -> (isDet : _) -> Gen MaybeEmpty $ VExpr mVTy isDet

public export
genVExpr0 : Fuel ->
            (Fuel -> (a : _) -> (b : _) -> Gen MaybeEmpty $ VExpr a b) =>
            (Fuel -> (a : _) -> Gen MaybeEmpty $ (b ** c ** BoolAnd a b c)) =>
            (Fuel -> (a : _) -> Gen MaybeEmpty $ RawValue a) =>
            (mVTy : _) -> Gen MaybeEmpty $ (isDet ** VExpr mVTy isDet)

public export
genVExpr : Fuel ->
           (Fuel -> (a : _) -> (b : _) -> Gen MaybeEmpty $ VExpr a b) =>
           (Fuel -> (a : _) -> Gen MaybeEmpty $ (b ** VExpr a b)) =>
           (Fuel -> (a : _) -> Gen MaybeEmpty $ (b ** c ** BoolAnd a b c)) =>
           (Fuel -> (a : _) -> Gen MaybeEmpty $ RawValue a) =>
           Gen MaybeEmpty $ (mVTy ** isDet ** VExpr mVTy isDet)

public export
genValue : Fuel ->
           (Fuel -> Gen MaybeEmpty (a ** b ** VExpr a b)) =>
           Gen MaybeEmpty Value

