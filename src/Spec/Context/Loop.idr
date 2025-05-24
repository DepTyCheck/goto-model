module Spec.Context.Loop

import public Spec.Context.Source
import public Debug.Trace

namespace Guarantee
  public export
  data Guarantee = GValue | GType | GNothing

  %name Guarantee g

  public export
  data VectGuarantee : Nat -> Type where
    Nil : VectGuarantee 0
    (::) : (g : Guarantee) -> (gs : VectGuarantee n) -> VectGuarantee (S n)

  %name VectGuarantee gs

  public export
  data IsWindedWithGValue' : (sr : Value) -> {-postR-}Value -> {-preUc-}Nat ->
                             {-postUc-}Nat -> Type where
    [search sr]
    IsWindedUndet' : IsWindedWithGValue' (JustV {vTy} {isDet = False} vExpr) (JustV $ Undet vTy uc) uc (S uc)
    IsWindedDet' : IsWindedWithGValue' (JustV {isDet = True} vExpr) (JustV vExpr) uc uc

  public export
  data IsWinded' : (sr : Value) -> (g : Guarantee) -> {-ir-}Value -> {-preUc-}Nat -> {-postUc-}Nat -> Type where
    [search sr g]
    -- TODO: will probably cause strange filtration
    IsWindedGValue' : IsWindedWithGValue' sr ir uc uc' => IsWinded' sr GValue ir uc uc'
    -- TODO: constants may also be not saved completely
    IsWindedGType' : IsWinded' (JustV {vTy} vExpr) GType (JustV $ Undet vTy uc) uc (S uc)
    IsWindedGNothing' : IsWinded' v GNothing Unkwn uc uc

  public export
  data AreWinded' : (savedRegs : VectValue n) -> (gs : VectGuarantee n) ->
                    {-initRegs-}VectValue n -> {-curUc-}Nat -> {-initUc-}Nat -> Type where
    [search savedRegs gs]
    AreWindedBase' : AreWinded' [] [] [] uc uc
    AreWindedStep' : {curUc' : _} ->
                     AreWinded' savedRegs gs initRegs curUc' uc ->
                     IsWinded' sr g ir curUc curUc' =>
                     AreWinded' (sr :: savedRegs) (g :: gs) (ir :: initRegs) curUc uc

  public export
  data AreWinded : (savedRegs : VectValue n) -> (gs : VectGuarantee n) ->
                   {-initRegs-}VectValue n -> {-initUc-}Nat -> Type where
    [search savedRegs gs]
    TheyAreWinded : {initUc : _} -> AreWinded' savedRegs gs initRegs 0 initUc => AreWinded savedRegs gs initRegs initUc

  -- TODO: causes fake filtration. CanUnwind must be built upon IsWinded',
  -- but Idris cannot handle it and further usage causes fighting with compiler bugs
  public export
  data CanUnwind : (ir : Value) -> Guarantee -> (fr : Value) -> Type where
    CanUnwindGValue : CanUnwind ir GValue ir
    CanUnwindGType : CanUnwind (JustV {vTy} initExpr) GType (JustV {vTy} finalExpr)
    CanUnwindGNothing : CanUnwind Unkwn GNothing fr

  public export
  data CanUnwindAll : (initRegs : VectValue n) -> (gs : VectGuarantee n) -> (finalRegs : VectValue n) -> Type where
    CanUnwindAllBase : CanUnwindAll [] [] []
    CanUnwindAllStep : CanUnwindAll initRegs gs finalRegs ->
                       CanUnwind ir g fr =>
                       CanUnwindAll (ir :: initRegs) (g :: gs) (fr :: finalRegs)

-- When loop starts, we save the current context and create a new one
-- For simplicity, we do not merge any free sources or sources from outer loops during the current loop
public export
data Loop : Nat -> Type where
  L : (savedRegs : VectValue n) -> {m : _} -> (savedSrcs : VectSource m n) -> (savedUc : Nat)
   -> (gs : VectGuarantee n) -> (initRegs : VectValue n)
   -> AreWinded savedRegs gs initRegs initUc
   => Loop n

%name Loop l

public export
data ListLoop : Nat -> Type where
  Nil : ListLoop n
  (::) : Loop n -> ListLoop n -> ListLoop n

%name ListLoop ls

namespace Maybe
  public export
  data MaybeLoop : Nat -> Type where
    Nothing : MaybeLoop n
    Just : Loop n -> MaybeLoop n

