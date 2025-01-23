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
  data IsKnown : ValueType -> Type where
    IIsKnown : IsKnown I
    BIsKnown : IsKnown B

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
  data DetValue : ValueType -> Type where
    DetI : Int32 -> DetValue I
    DetB : Bool -> DetValue B

  public export
  data ValueExpr : ValueType -> Bool -> Type where
    Det : (vTy : ValueType) -> (rawV : DetValue vTy) -> ValueExpr vTy True
    Undet : (vTy : ValueType) -> (idx : Nat) -> ValueExpr vTy False
    Op : (idx : Nat) -> (vop : ValueOp) -> ValueExpr vTyL isDetL -> ValueExpr vTyR isDetR ->
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
         ItIsAddValueTypes => V I True $ Det I $ DetI $ (fst $ getI vExprL) + (fst $ getI vExprR)
         ItIsAndValueTypes => V B True $ Det B $ DetB $ (fst $ getB vExprL) && (fst $ getB vExprR)
         ItIsOrValueTypes => V B True $ Det B $ DetB $ (fst $ getB vExprL) || (fst $ getB vExprR)
    where
      getI : (vExpr : ValueExpr I True) -> (x ** vExpr = (Det I $ DetI x))
      getI (Det I $ DetI x) = (x ** Refl)

      getB : (vExpr : ValueExpr B True) -> (b ** vExpr = (Det B $ DetB b))
      getB (Det B $ DetB b) = (b ** Refl)


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
      (::) : (Nat, VectValue n) {-context at the moment of the jump-} -> ListSource n -> ListSource n

    public export
    data Concat : (leftSs : ListSource n) -> (rightSs : ListSource n) -> ListSource n -> Type where
      [search leftSs rightSs]
      ConcatBase : Concat [] ss ss
      ConcatStep : Concat ss1' ss2 ss -> Concat (s :: ss1') ss2 (s :: ss)

    public export
    data Length : (ss : ListSource n) -> Nat -> Type where
      [search ss]
      LengthEmpty : Length [] Z
      LengthNonEmpty : Length ss' l' -> Length (s :: ss') (S l')

    public export
    data Index : (i : Fin l) -> (ss : ListSource n) -> Length ss l => (Nat, VectValue n) -> Type where
      [search i ss]
      IndexBase : Index FZ (s :: ss') @{_} s
      IndexStep : Index i' ss' @{lenPrf'} s -> Index (FS i') (s' :: ss') @{LengthNonEmpty lenPrf'} s

  namespace Guarantee
    public export
    data Guarantee = SavesValue | SavesType | SavesNothing

    -- TODO: or name it ListGuarantee?
    -- TODO: just SavesValue must become (SavesType True)
    public export
    data Guarantees : (n : Nat) -> Type where
      Nil : Guarantees 0
      (::) : Guarantee -> Guarantees n -> Guarantees (S n)

  namespace Loop
    public export
    record Loop (n : Nat) where
      constructor L

      savedContext : ({-undeterminedCount-}Nat, {-regs-}VectValue n)
      initialContext : VectValue n -- context at the moment of the loop iteration beginning
      contextGuarantees : Guarantees n
      lockedSources : ListSource n

    public export
    data ListLoop : (n : Nat) -> Type where
      Nil : ListLoop n
      (::) : Loop n -> ListLoop n -> ListLoop n

  public export
  record Context (n : Nat) where
    constructor Ctx

    openLoops : ListLoop n
    undeterminedCount : Nat
    registers : VectValue n
    isInLinearBlock : Bool
    freeSources : ListSource n
  
  %name Context ctx
  
  data Finished : Context n -> Type where
    -- TODO: actually, False can be omitted, but just to be clear for now
    CtxIsFinished : Finished (Ctx [] _ _ False [])

namespace Program
  public export
  data PickHelper : (ss : ListSource n) -> (css : ListSource n) -> Nat -> VectValue n -> ListSource n -> Type where
    [search ss css]
    PickMiss : PickHelper ss' (s :: css) resUc resVs resSs => PickHelper (s :: ss') css resUc resVs resSs
    PickHit : Concat ss' css resSs => PickHelper ((uc, regs) :: ss') css uc regs resSs
  
  -- TODO: only simple case with 1 picked source covered. There is also
  -- complex case with many picked sources and merge of their values.
  -- Also, merge may require to introduce new undetermined values
  public export
  data Pick : (ss : ListSource n) -> Nat -> VectValue n -> ListSource n -> Type where
    [search ss]
    JustPick : PickHelper ss [] resUc resVs resSs => Pick ss resUc resVs resSs

  -- It is crucial to erase Ops, because otherwise the further dependency analysis in the unwinding step is crazy
  public export
  data ValueWinding : (uc : Nat) -> (oldV : Value) -> Nat -> Value -> Type where
    [search uc oldV]
    ResetUndetIndex : ValueWinding uc (V vTy False $ Undet ? oldIdx) (S uc) (V vTy False $ Undet ? uc) 
    EraseOp : ValueWinding uc (V vTy False $ Op oldIdx vop vExprL vExprR @{ovtPrf} @{notAllPrf}) (S uc) (V vTy False $ Undet ? uc)
    SkipDet : ValueWinding uc (V vTy True vExpr) uc (V vTy True vExpr)

  public export
  data ContWinding : {-current values-}VectValue n -> Guarantees n -> Nat -> VectValue n -> Type where
    JustGuarantees : ContWinding [] [] Z []
    GuaranteesValue : ContWinding regs' g' contUc' contRegs' =>
                      IsKnown vTy =>
                      ValueWinding contUc' (V vTy isDet vExpr) contUc v =>
                      ContWinding ((V vTy isDet vExpr) :: regs') (SavesValue :: g') contUc (v :: contRegs')
    GuaranteesType : ContWinding regs' g' contUc' contRegs' =>
                     IsKnown vTy =>
                     ContWinding ((V vTy isDet vExpr) :: regs') (SavesType :: g') (S contUc') ((V vTy False $ Undet ? contUc') :: contRegs')
    GuaranteesNothing : ContWinding regs' g' contUc contRegs' =>
                        ContWinding (v' :: regs') (SavesNothing :: g') contUc ((V U False $ Undet ? 0) :: contRegs')

  public export
  data IsSankIn : {-post-}Context n -> {-pre-}Context n -> Type where
    -- TODO: potentially, we can allow to enter a context with loops from the outside
    ItIsSankInViaFree : Pick fs contUc contRegs contFs =>
                        Ctx [] contUc contRegs True contFs `IsSankIn` Ctx [] uc regs False fs
    ItIsSankInViaLocked : Pick ls contUc contRegs contLs =>
                          Ctx ((L savedCtx initCtx g contLs) :: ols') contUc contRegs True fs `IsSankIn` Ctx ((L savedCtx initCtx g ls) :: ols') uc regs False fs
    ItIsSankInWithLoop : Ctx contOls' contUc' contRegs' True contFs' `IsSankIn` Ctx ols uc regs False fs =>
                         -- context to-loop update happens here
                         ContWinding contRegs' g contUc contRegs =>
                         Ctx ((L (contUc', contRegs') contRegs g []) :: contOls') contUc contRegs True contFs' `IsSankIn` Ctx ols uc regs False fs

  public export
  data ForwardEdge : {-pre-}Context n -> {-post-}Context n -> Type where
    -- When a forward edge is attached in a not linear context,
    -- the edge relates to the last completed linear block
    Free : ForwardEdge (Ctx [] uc regs _ fs) $ Ctx [] uc regs False ((uc, regs) :: fs)
    Locked : ForwardEdge (Ctx ((L savedCtx initCtx g ls) :: ols') uc regs _ fs) $ Ctx ((L savedCtx initCtx g $ (uc, regs) :: ls) :: ols') uc regs False fs

  public export
  data IsMet : Guarantee -> Value -> Value -> Type where
    ValueIsMet : IsMet SavesValue v v
    TypeIsMet : IsMet SavesType (V vTy _ _) (V vTy _ _)

  public export
  data NotSame : Nat -> Nat -> Type where
    NotSameLeftBase : NotSame Z (S m')
    NotSameRightBase : NotSame (S n') Z
    NotSameStep : NotSame n m => NotSame (S n) (S m)

  public export
  data SelfDepends : (initExpr : ValueExpr vTy initIsDet) -> (vExpr : ValueExpr vTy isDet) -> Bool -> Type where
    [search initExpr vExpr]
    SelfDependsDet : SelfDepends _ (Det _ _) True
    SelfDependsUndet : SelfDepends (Undet vTy i) (Undet vTy i) True
    SelfDependsFalse : NotSame i j => SelfDepends (Undet vTy i) (Undet vTy j) False
    SelfDependsStep : SelfDepends initExpr vExprL sdL =>
                      SelfDepends initExpr vExprR sdR =>
                      BoolAnd sdL sdR sd =>
                      SelfDepends initExpr (Op _ _ vExprL vExprR @{ovtPrf} @{notAllPrf}) sd

  public export
  data ExprUnwinding : (uc' : Nat) -> (savedExpr : ValueExpr vTy savedIsDet) -> (initExpr : ValueExpr vTy initIsDet) -> (finalExpr : ValueExpr vTy isDet) -> Nat -> ValueExpr vTy isDet -> Type where
    [search uc' savedExpr initExpr finalExpr]
    ExprUnwindingId : ExprUnwinding uc savedExpr initExpr initExpr uc savedExpr
    ExprUnwindingDet : ExprUnwinding uc savedExpr (Undet _ _) (Det vTy rawV) uc (Det ? rawV)
    ExprUnwindingOp : ExprUnwinding uc' savedExpr initExpr (Op _ _ _ _ @{ovtPrf} @{notAllPrf}) (S uc') (Undet ? uc')

  public export
  data Squash : Nat -> ValueExpr vTy savedIsDet -> ValueExpr vTy initIsDet -> ValueExpr vTy isDet -> Nat -> ValueExpr vTy isDet -> Type where
    SquashSelfRec : SelfDepends initExpr finalExpr True =>
                    ExprUnwinding uc' savedExpr initExpr finalExpr uc vExpr =>
                    Squash uc' savedExpr initExpr finalExpr uc vExpr 
    -- If it is not self-recursive, then it must be not a constant
    SquashNotSelfRec : SelfDepends initExpr finalExpr False =>
                       Squash uc' savedExpr initExpr finalExpr (S uc') (Undet ? uc')

  public export
  data ResetIndex : {isDet : _} -> {vTy : _} -> Nat -> ValueExpr vTy isDet -> Nat -> ValueExpr vTy isDet -> Type where
    ResetIndexHit : ResetIndex {isDet=False} {vTy} uc' vExpr' (S uc') $ Undet vTy uc'
    ResetIndexMiss : ResetIndex {isDet=True} uc v uc v

  public export
  data ValueUnwinding : {-uc-}Nat -> {-saved values to build the result-}Value -> Guarantee -> {-init-}Value -> {-final-}Value -> {-the result uc-}Nat -> {-the result-}Value -> Type where
    FinalValueIsPreserved : ValueUnwinding uc savedV SavesValue initV initV uc savedV
    FinalTypeIsPreserved : Squash uc' savedExpr initExpr finalExpr uc vExpr =>
                           ValueUnwinding uc' (V vTy savedIsDet savedExpr) SavesType (V vTy initIsDet initExpr) (V vTy isDet finalExpr) uc (V vTy isDet vExpr)
    FinalIsIntroduced : IsKnown vTy =>
                        ResetIndex uc' vExpr' uc vExpr =>
                        ValueUnwinding uc' _ SavesNothing _ (V vTy isDet vExpr') uc (V vTy isDet vExpr)
    -- TODO: maybe I should work differently with completely unknown values or count them properly
    FinalIsUnknown : ValueUnwinding uc savedV SavesNothing (V _ _ _) (V U _ _) uc (V U False $ Undet U 0)

  public export
  data ContUnwinding : (Nat, VectValue n) -> VectValue n -> Guarantees n -> Nat -> VectValue n -> Nat -> VectValue n -> Type where
    -- 2 major steps: summarize the iteration and make the new context
    ContUnwindingBase : ContUnwinding (savedUc, []) [] [] uc [] savedUc []
    ContUnwindingStep : ContUnwinding (savedUc, savedRegs') initRegs' g' uc finalRegs' contUc' contRegs' =>
                        ValueUnwinding contUc' savedV vg initV finalV contUc contV =>
                        ContUnwinding (savedUc, savedV :: savedRegs') (initV :: initRegs') (vg :: g') uc (finalV :: finalRegs') contUc (contV :: contRegs') 


  public export
  data IsStrictlyMonotoneValueExpr : ValueExpr I isDet -> ValueExpr I isDet -> Type where
    ItIsInc : IsStrictlyMonotoneValueExpr initExpr (Op _ Add initExpr (Det I $ DetI 1) @{ovtPrf} @{notAllPrf})
    -- TODO: analyze initExpr and vExpr

  public export
  data HasStrictlyMonotoneValue : VectValue n -> VectValue n -> Type where
    StrictlyMonotoneValueHere : IsStrictlyMonotoneValueExpr initExpr finalExpr => HasStrictlyMonotoneValue ((V I isDet initExpr) :: initRegs') ((V I isDet finalExpr) :: finalRegs')
    StrictlyMonotoneValueThere : HasStrictlyMonotoneValue initRegs' finalRegs' => HasStrictlyMonotoneValue (v1 :: initRegs') (v2 :: finalRegs')

  public export
  data Edge : {-pre-}Context n -> {-post-}Context n -> Type where
    Backward : HasStrictlyMonotoneValue initCtx regs =>
               ContUnwinding savedCtx initCtx g uc regs contUc contRegs => -- context from-loop update happens here
               Concat ls fs contFs =>
               Edge (Ctx ((L savedCtx initCtx g ls) :: ols') uc regs True fs) (Ctx ols' contUc contRegs False contFs)
    Forward : ForwardEdge ctx contCtx -> Edge ctx contCtx

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

  Source0 : Program (Ctx [] uc regs False fs) ->
            Program (Ctx [] uc regs True fs)
  Source1 : Edge (Ctx ols uc regs True fs) (Ctx contOls contUc contRegs False contFs) =>
            Program (Ctx contOls contUc contRegs False contFs) ->
            Program (Ctx ols uc regs True fs)
  Source2 : Edge (Ctx ols uc regs True fs) (Ctx contOls' contUc' contRegs' False contFs') =>
            ForwardEdge (Ctx contOls' contUc' contRegs' False contFs') (Ctx contOls contUc contRegs False contFs) =>
            Program (Ctx contOls contUc contRegs False contFs) ->
            Program (Ctx ols uc regs True fs)

  Finish : Finished ctx => Program ctx

%name Program prog


test0 : Program {n=2} $ Ctx [] Z [V _ _ (Det _ $ DetI 1), V _ _ (Det _ $ DetB True)] True []
test0 = Assign 0 1 $
        Source0 $ 
        Finish

test1 : Program {n=2} $ Ctx [] 1 [V _ _ (Undet _ 0), V _ _ (Det _ $ DetB True)] True []
test1 = Assign 0 1 $
        Source0 $
        Finish

test2 : Program {n=2} $ Ctx [] 1 [V _ _ (Undet I 0), V _ _ (Det _ $ DetI 1)] True []
test2 = Source1 @{Forward Free} $
        -- Program {n=2} $ Ctx [] 1 [V _ _ (Undet I 0), V _ _ (Det _ $ DetI 1)] False [(1, [...])]
        Sink @{ItIsSankInWithLoop {g=[SavesType, SavesValue]} @{ItIsSankInViaFree @{JustPick @{PickHit}}} @{GuaranteesType @{GuaranteesValue @{JustGuarantees}}}} $
                                      
        -- After ItIsSankInViaFree
        -- Program {n=2} $ Ctx [] 1 [V _ _ (Undet I 0), V _ _ (Det _ $ DetI 1)] True []
        -- After ItIsSankInWithLoop
        RegOp Add 0 0 1 $
        -- Program {n=2} $ Ctx [L (1, [V I False (Undet I 0), V I True (Det I (DetI 1))])
        --                        [V I False (Undet I 0), V I True (Det I (DetI 1))] 
        --                        [SavesType, SavesValue]
        --                        []
        --                     ] 2 [ V I False (Op 1 Add (Undet I 0) (Det I (DetI 1)))
        --                         , V I True (Det I (DetI 1))
        --                         ] True []
        Source2 @{Backward @{%search} @{ContUnwindingStep @{ContUnwindingStep @{ContUnwindingBase} @{FinalValueIsPreserved}} @{FinalTypeIsPreserved @{SquashSelfRec @{SelfDependsStep}}}}} @{Free} $
        Sink @{ItIsSankInViaFree @{JustPick @{PickHit}}} $
        Source0 $
        Finish

test2' : SelfDepends (Undet I 0) (Op 1 Add (Undet I 0) (Det _ $ DetI 1)) True
test2' = SelfDependsStep @{SelfDependsUndet} @{SelfDependsDet}
