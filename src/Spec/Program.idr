module Spec.Program

import Data.Fin
import Data.Vect
import Decidable.Equality

import Spec.Tree


%default total


namespace Logic
  public export
  data NotAll : Bool -> Bool -> Type where
    NotFirst : NotAll False _
    NotSecond : NotAll _ False

  public export
  data BoolAnd : Bool -> Bool -> Bool -> Type where
    TrueAndTrue : BoolAnd True True True
    FalseAndAny : BoolAnd False _ False
    AnyAndFalse : BoolAnd _ False False


namespace Value
  public export
  data ValueType = U | I | B
  
  %name ValueType vTy

  public export
  data ValueOp = Add | And | Or

  %name ValueOp vop

  public export
  data IsOpValueTypes : (vop : ValueOp) -> (vTyL : ValueType) -> (vTyR : ValueType) -> ValueType -> Type where
    [search vop vTyL vTyR]
    ItIsAddValueTypes : IsOpValueTypes Add I I I
    ItIsAndValueTypes : IsOpValueTypes And B B B
    ItIsOrValueTypes : IsOpValueTypes Or B B B

  %name IsOpValueTypes ovtPrf

  public export
  data ValueExpr : ValueType -> Bool -> Type where
    -- TODO: definitely can be generalized
    DetI : Int32 -> ValueExpr I True
    DetB : Bool -> ValueExpr B True
    UndetI : ValueExpr I False
    UndetB : ValueExpr B False
    Op : (opIdx : Nat) -> (vop : ValueOp) -> ValueExpr vTyL isDetL -> ValueExpr vTyR isDetR ->
         IsOpValueTypes vop vTyL vTyR vTy => NotAll isDetL isDetR =>
         ValueExpr vTy False

  %name ValueExpr vExpr

  public export
  record Value where
    constructor V

    type : ValueType
    isDetermined : Bool
    raw : ValueExpr type isDetermined

  %name Value v

  public export
  data Satisfied : Value -> Value -> Type where

  public export
  data IsOpValues : (vop : ValueOp) -> (lv : Value) -> (rv : Value) -> ValueType -> Type where
    [search vop lv rv]
    ItIsAddValues : IsOpValues Add (V I _ _) (V I _ _) I
    ItIsAndValues : IsOpValues And (V B _ _) (V B _ _) B
    ItIsOrValues : IsOpValues Or (V B _ _) (V B _ _) B

  public export
  opValuesAreOpValueTypes : IsOpValues vop lv rv vTy -> IsOpValueTypes vop lv.type rv.type vTy

  public export
  produce : (undetC : Nat) -> (vop : ValueOp) -> (lv : Value) -> (rv : Value) -> {vTy : _} -> IsOpValues vop lv rv vTy => Value
  produce undetC vop (V vTyL False vExprL) (V vTyR isDetR vExprR) @{ovPrf} =
    V vTy False $ Op undetC vop vExprL vExprR @{opValuesAreOpValueTypes ovPrf}
  produce undetC vop (V vTyL True vExprL) (V vTyR False vExprR) @{ovPrf} =
    V vTy False $ Op undetC vop vExprL vExprR @{opValuesAreOpValueTypes ovPrf}
  -- TODO: cannot make case split on ovPrf
  produce _ vop (V vTyL True vExprL) (V vTyR True vExprR) @{ovPrf} = do
    let ovtPrf = opValuesAreOpValueTypes ovPrf
    case ovtPrf of
         ItIsAddValueTypes => V I True $ DetI $ (fst $ getI vExprL) + (fst $ getI vExprR)
         ItIsAndValueTypes => V B True $ DetB $ (fst $ getB vExprL) && (fst $ getB vExprR)
         ItIsOrValueTypes => V B True $ DetB $ (fst $ getB vExprL) || (fst $ getB vExprR)
    where
      getI : (vExpr : ValueExpr I True) -> (x ** vExpr = DetI x)
      getI (DetI x) = (x ** Refl)

      getB : (vExpr : ValueExpr B True) -> (b ** vExpr = DetB b)
      getB (DetB b) = (b ** Refl)


  public export
  data VectValue : Nat -> Type where
    Nil : VectValue 0
    (::) : Value -> VectValue n -> VectValue (S n)

  %name VectValue vs

  public export
  data HasType : Fin n -> ValueType -> VectValue n -> Type where
    HasTypeBase : HasType FZ vTy $ (V vTy _ _) :: vs'
    HasTypeStep : HasType i vTy vs' -> HasType (FS i) vTy (v :: vs')

  %name HasType htPrf
  
  public export
  data Index : (i : Fin n) -> (vs : VectValue n) -> Value -> Type where
    [search i vs]
    IndexBase : Index FZ (v :: vs) v
    IndexStep : Index i' vs v -> Index (FS i') (v' :: vs) v

  public export
  index : Fin n -> VectValue n -> Value
  index FZ (v :: vs) = v
  index (FS i') (v :: vs) = index i' vs

  public export
  replaceAt : Fin n -> Value -> VectValue n -> VectValue n
  replaceAt FZ v (v1 :: vs) = v :: vs
  replaceAt (FS i') v (v1 :: vs) = v1 :: replaceAt i' v vs

  public export
  duplicate : (dst : Fin n) -> (src : Fin n) -> VectValue n -> VectValue n
  duplicate dst src vs = replaceAt dst (index src vs) vs


namespace Context
  namespace Source
    public export
    data ListSource : (n : Nat) -> Type where
      Nil : ListSource n
      (::) : VectValue n {-context at the moment of the jump-} -> ListSource n -> ListSource n

    public export
    data Concat : ListSource n -> ListSource n -> ListSource n -> Type where
      ConcatBase : Concat [] ss ss
      ConcatStep : Concat ss1' ss2 ss -> Concat (s :: ss1') ss2 (s :: ss)

    public export
    data Length : (ss : ListSource n) -> Nat -> Type where
      LengthEmpty : Length [] Z
      LengthNonEmpty : Length ss' l' -> Length (s :: ss') (S l')

    public export
    data Index : (i : Fin l) -> (ss : ListSource n) -> Length ss l => VectValue n -> Type where
      [search i ss]
      IndexBase : Index FZ (s :: ss') @{_} s
      IndexStep : Index i' ss' @{lenPrf'} s -> Index (FS i') (s' :: ss') @{LengthNonEmpty lenPrf'} s

  namespace Loop
    public export
    data ListLoop : (n : Nat) -> Type where
      Nil : ListLoop n
      (::) : (VectValue n {-ctx guarantees-}, VectValue n {-current diff-}, ListSource n {-locked sources-}) -> ListLoop n -> ListLoop n

  public export
  record Context (n : Nat) where
    constructor Ctx
  
    -- Again, goto = source -> sink
    -- Locked source = it is inside of an unended loop
    -- Free source = it is any other source available

    -- info about current opened loops (context guarantees & saved values diff & locked sources)
    -- Again, goto = source -> sink
    -- TODO: only 1 loop is allowed now
    openedLoops : ListLoop n
    -- info about current values (only regs for now)
    undeterminedCount : Nat -- required to introduce new undetermined variables
    values : VectValue n
    isInLinearBlock : Bool
    -- info about free sources & their contexts
    freeSources : ListSource n

  -- For new sources in a loop (locked) I must save current values 
  
  %name Context ctx
  
  data Finished : Context n -> Type where
    CtxIsFinished : Finished (Ctx [] _ _ _ [])

namespace Program
  public export
  data PickHelper : (ss : ListSource n) -> (css : ListSource n) -> VectValue n -> ListSource n -> Type where
    [search ss css]
    PickMiss : PickHelper ss' (s :: css) resVs resSs => PickHelper (s :: ss') css resVs resSs
    PickHit : Concat ss' css resSs => PickHelper (s :: ss') css s resSs
  
  -- TODO: only simple case with 1 picked source covered. There is also
  -- complex case with many picked sources and merge of their values. It is not simple to implement due to
  -- transposition of lists of vects into vect of lists (merge of the selected sources)
  -- Also, merge may require to introduce new undetermined values
  public export
  data Pick : (ss : ListSource n) -> VectValue n -> ListSource n -> Type where
    [search ss]
    PickBootstrap : PickHelper (s :: ss') [] resVs resSs => Pick (s :: ss') resVs resSs

  public export
  data IsSankIn : Context n -> Context n -> Type where
    ItIsSankInViaFree : Pick fs contRegs contFs =>
                        Ctx ols uc contRegs True contFs `IsSankIn` Ctx ols uc regs False fs
    ItIsSankInViaLocked : Pick ls contRegs contLs =>
                          Ctx ((g, d, contLs) :: ols') uc contRegs True fs `IsSankIn` Ctx ((g, d, ls) :: ols') uc regs False fs
    ItIsSankInWithLoop : Ctx contOls contUc contRegs True contFs `IsSankIn` Ctx ols uc regs False fs =>
                         -- update uc, regs due to a new loop
                         IsSankIn (Ctx ((g, d, ls) :: contOls) contUc contRegs True contFs) $ Ctx ols uc regs False fs

  public export
  data ForwardEdge : Context n -> Context n -> Type where
    -- When a forward edge is attached in a not linear context,
    -- the edge relates to the last completed linear block
    Free : ForwardEdge (Ctx [] uc regs False (regs :: fs)) (Ctx [] uc regs _ fs)
    Locked : ForwardEdge (Ctx ((g, d, regs :: ls) :: ols') uc regs False fs) (Ctx ((g, d, ls) :: ols') uc regs _ fs)

  public export
  data Edge : Context n -> Context n -> Type where
    Backward : -- guarantees are reached
               -- decreasing/increasing variable exists
               -- update the context
               Concat fs ls contFs =>
               Edge (Ctx ols' contUc contRegs False contFs) (Ctx ((g, d, ls) :: ols') uc regs True fs)
    Forward : ForwardEdge contCtx ctx -> Edge contCtx ctx

public export
data Program : Context n -> Type where
  -- Linear Block
  Assign : (target : Fin n) -> (i : Fin n) ->
           Program (Ctx ols uc (duplicate target i regs) True fs) ->
           Program $ Ctx ols uc regs True fs
  RegOp : (vop : ValueOp) -> (target : Fin n) -> (li : Fin n) -> (ri : Fin n) ->
          {ols : _} -> {uc : _} -> {regs : _} -> {fs : _} -> {lv, rv : _} -> {vTy : _} ->
          Index li regs lv => Index ri regs rv => IsOpValues vop lv rv vTy =>
          let newValue : ?; newValue = produce uc vop lv rv in  -- TODO: reduce function?...
          Program (Ctx ols (if newValue.isDetermined then uc else (S uc)) (replaceAt target newValue regs) True fs) ->
          Program $ Ctx ols uc regs True fs

  -- Control Flow
  Sink : contCtx `IsSankIn` ctx => Program contCtx -> Program ctx

  Source0 : Program (Ctx ols uc regs False fs) -> Program (Ctx ols uc regs True fs)
  Source1 : Edge (Ctx contOls contUc contRegs False contFs) (Ctx ols uc regs True fs) ->
            Program (Ctx contOls contUc contRegs False contFs) ->
            Program (Ctx ols uc regs True fs)
  Source2 : Edge (Ctx contOls' contUc' contRegs' False contFs') (Ctx ols uc regs True fs) ->
            ForwardEdge (Ctx contOls contUc contRegs False contFs) (Ctx contOls' contUc' contRegs' False contFs') ->
            Program (Ctx contOls contUc contRegs False contFs) ->
            Program (Ctx ols uc regs True fs)

  Finish : Finished ctx => Program ctx

%name Program prog
