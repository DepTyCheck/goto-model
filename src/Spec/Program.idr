module Spec.Program

import public Data.Fin
import Data.Vect
import Decidable.Equality


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

namespace Nat
  public export
    data NotSame : Nat -> Nat -> Type where
      NotSameLeftBase : NotSame Z (S m')
      NotSameRightBase : NotSame (S n') Z
      NotSameStep : NotSame n m => NotSame (S n) (S m)

namespace Value
  public export
  data VType = I | B
  
  %name VType vTy

  public export
  data MaybeVType = Nothing | Just VType

  public export
  data ValueOp = Add | And | Or

  %name ValueOp vop

  public export
  data IsOpVTypes : (vop : ValueOp) -> (vTyL : VType) -> (vTyR : VType) -> VType -> Type where
    [search vop vTyL vTyR]
    ItIsAddVTypes : IsOpVTypes Add I I I
    ItIsAndVTypes : IsOpVTypes And B B B
    ItIsOrVTypes : IsOpVTypes Or B B B

  %name IsOpVTypes ovtPrf

  public export
  data RawValue : VType -> Type where
    RawI : Int32 -> RawValue I
    RawB : Bool -> RawValue B

  public export
  data VExpr : MaybeVType -> Bool -> Type where
    Unkwn : VExpr Nothing False
    Det : {vTy : _} -> (rawV : RawValue vTy) -> VExpr (Just vTy) True
    Undet : (vTy : VType) -> (idx : Nat) -> VExpr (Just vTy) False
    Op : (idx : Nat) -> (vop : ValueOp) -> VExpr (Just vTyL) isDetL -> VExpr (Just vTyR) isDetR ->
         IsOpVTypes vop vTyL vTyR vTy => NotAll isDetL isDetR =>
         VExpr (Just vTy) False

  %name VExpr vExpr

  %hint
  public export
  unkwnIsSingleton : (vExpr : VExpr Nothing isDet) -> vExpr = Unkwn
  unkwnIsSingleton Unkwn = Refl

  public export
  determinedIsNeverUnkwn : (vExpr : VExpr mVTy True) -> (vTy ** mVTy = Just vTy)
  determinedIsNeverUnkwn (Det {vTy} rawV) = (vTy ** Refl)

  public export
  record Value where
    constructor V

    mtype : MaybeVType
    isDetermined : Bool
    raw : VExpr mtype isDetermined

  %name Value v

  public export
  data IsOpValues : (vop : ValueOp) -> (lv : Value) -> (rv : Value) -> VType -> Type where
    [search vop lv rv]
    ItIsAddValues : IsOpValues Add (V (Just I) _ _) (V (Just I) _ _) I
    ItIsAndValues : IsOpValues And (V (Just B) _ _) (V (Just B) _ _) B
    ItIsOrValues : IsOpValues Or (V (Just B) _ _) (V (Just B) _ _) B

  public export
  opValuesAreKnown : IsOpValues vop lv rv vTy -> ((vTyL ** lv.mtype = Just vTyL), (vTyR ** rv.mtype = Just vTyR))
  opValuesAreKnown ItIsAddValues = ((I ** Refl), (I ** Refl))
  opValuesAreKnown ItIsAndValues = ((B ** Refl), (B ** Refl))
  opValuesAreKnown ItIsOrValues = ((B ** Refl), (B ** Refl))

  public export
  opValuesAreOpVTypes : IsOpValues vop (V (Just vTyL) _ _) (V (Just vTyR) _ _) vTy -> IsOpVTypes vop vTyL vTyR vTy
  opValuesAreOpVTypes ItIsAddValues = ItIsAddVTypes
  opValuesAreOpVTypes ItIsAndValues = ItIsAndVTypes
  opValuesAreOpVTypes ItIsOrValues = ItIsOrVTypes

  public export
  produce : (undetC : Nat) -> (vop : ValueOp) -> (lv : Value) -> (rv : Value) -> {vTy : _} -> IsOpValues vop lv rv vTy => Value
  produce undetC vop (V mVTyL False vExprL) (V mVTyR isDetR vExprR) @{ovPrf} = do
    let ((vTyL ** Refl), (vTyR ** Refl)) = opValuesAreKnown ovPrf
    V (Just vTy) False $ Op {vTyL} {vTyR} undetC vop vExprL vExprR @{opValuesAreOpVTypes ovPrf}
  produce undetC vop (V mVTyL True vExprL) (V mVTyR False vExprR) @{ovPrf} = do
    let ((vTyL ** Refl), (vTyR ** Refl)) = opValuesAreKnown ovPrf
    V (Just vTy) False $ Op undetC vop vExprL vExprR @{opValuesAreOpVTypes ovPrf}
  -- TODO: cannot make case split on ovPrf, compiler fails
  produce _ vop (V mVTyL True vExprL) (V mVTyR True vExprR) @{ovPrf} = do
    let ((vTyL ** Refl), (vTyR ** Refl)) = opValuesAreKnown ovPrf
    let ovtPrf = opValuesAreOpVTypes ovPrf
    case ovtPrf of
         ItIsAddVTypes => V (Just I) True $ Det $ RawI $ (fst $ getI vExprL) + (fst $ getI vExprR)
         ItIsAndVTypes => V (Just B) True $ Det $ RawB $ (fst $ getB vExprL) && (fst $ getB vExprR)
         ItIsOrVTypes => V (Just B) True $ Det $ RawB $ (fst $ getB vExprL) || (fst $ getB vExprR)
    where
      getI : (vExpr : VExpr (Just I) True) -> (x ** vExpr = (Det $ RawI x))
      getI (Det $ RawI x) = (x ** Refl)

      getB : (vExpr : VExpr (Just B) True) -> (b ** vExpr = (Det $ RawB b))
      getB (Det $ RawB b) = (b ** Refl)


  public export
  data VectValue : Nat -> Type where
    Nil : VectValue 0
    (::) : Value -> VectValue n -> VectValue (S n)

  %name VectValue vs

  public export
  data HasType : Fin n -> VType -> VectValue n -> Type where
    HasTypeBase : HasType FZ vTy $ (V (Just vTy) _ _) :: vs'
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

    public export
    data IsMet : Guarantee -> Value -> Value -> Type where
      ValueIsMet : IsMet SavesValue v v
      TypeIsMet : IsMet SavesType (V (Just vTy) _ _) (V (Just vTy) _ _)

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
    ResetUndetIndex : ValueWinding uc (V (Just vTy) False $ Undet ? oldIdx) (S uc) (V (Just vTy) False $ Undet ? uc)
    EraseOp : ValueWinding uc (V (Just vTy) False $ Op oldIdx vop vExprL vExprR @{ovtPrf} @{notAllPrf}) (S uc) (V (Just vTy) False $ Undet ? uc)
    SkipDet : ValueWinding uc (V (Just vTy) True vExpr) uc (V (Just vTy) True vExpr)

  public export
  data ContWinding : (regs : VectValue n) -> (gs : Guarantees n) ->
                     Nat -> VectValue n -> Type where
    [search regs gs]
    JustGuarantees : ContWinding [] [] Z []
    GuaranteesValue : ContWinding regs' g' contUc' contRegs' =>
                      ValueWinding contUc' (V (Just vTy) isDet vExpr) contUc v =>
                      ContWinding ((V (Just vTy) isDet vExpr) :: regs') (SavesValue :: g') contUc (v :: contRegs')
    GuaranteesType : ContWinding regs' g' contUc' contRegs' =>
                     ContWinding ((V (Just vTy) isDet vExpr) :: regs') (SavesType :: g') (S contUc') ((V (Just vTy) False $ Undet ? contUc') :: contRegs')
    GuaranteesNothing : ContWinding regs' g' contUc contRegs' =>
                        ContWinding (v' :: regs') (SavesNothing :: g') contUc ((V Nothing False Unkwn) :: contRegs')

  public export
  data IsSankIn : {-post-}Context n -> (ctx : Context n) -> Type where
    [search ctx]
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
  data ForwardEdge : (ctx : Context n) -> {-post-}Context n -> Type where
    [search ctx]
    -- When a forward edge is attached in a not linear context,
    -- the edge relates to the last completed linear block
    Free : ForwardEdge (Ctx [] uc regs _ fs) $ Ctx [] uc regs False ((uc, regs) :: fs)
    Locked : ForwardEdge (Ctx ((L savedCtx initCtx g ls) :: ols') uc regs _ fs) $ Ctx ((L savedCtx initCtx g $ (uc, regs) :: ls) :: ols') uc regs False fs


  public export
  data SelfDepends : (initExpr : VExpr mVTy initIsDet) -> (vExpr : VExpr mVTy isDet) ->
                     Bool -> Type where
    [search initExpr vExpr]
    SelfDependsDet : SelfDepends _ (Det _) True
    SelfDependsUndet : SelfDepends (Undet vTy i) (Undet vTy i) True
    SelfDependsFalse : NotSame i j => SelfDepends (Undet vTy i) (Undet vTy j) False
    SelfDependsStep : SelfDepends initExpr vExprL sdL =>
                      SelfDepends initExpr vExprR sdR =>
                      BoolAnd sdL sdR sd =>
                      SelfDepends initExpr (Op _ _ vExprL vExprR @{ovtPrf} @{notAllPrf}) sd

  public export
  data ExprUnwinding : (uc' : Nat) -> (savedExpr : VExpr mVTy savedIsDet) ->
                       (initExpr : VExpr mVTy initIsDet) -> (finalExpr : VExpr mVTy isDet) ->
                       Nat -> VExpr mVTy isDet -> Type where
    [search uc' savedExpr initExpr finalExpr]
    ExprUnwindingId : ExprUnwinding uc savedExpr initExpr initExpr uc savedExpr
    ExprUnwindingDet : ExprUnwinding uc savedExpr (Undet _ _) (Det rawV) uc (Det rawV)
    ExprUnwindingOp : ExprUnwinding uc' savedExpr initExpr (Op _ _ _ _ @{ovtPrf} @{notAllPrf}) (S uc') (Undet ? uc')

  public export
  data Squash : (uc' : Nat) -> (savedExpr : VExpr (Just vTy) savedIsDet) ->
                (initExpr : VExpr (Just vTy) initIsDet) -> (finalExpr : VExpr (Just vTy) isDet) ->
                Nat -> VExpr (Just vTy) isDet -> Type where
    [search uc' savedExpr initExpr finalExpr]
    SquashSelfRec : SelfDepends initExpr finalExpr True =>
                    ExprUnwinding uc' savedExpr initExpr finalExpr uc vExpr =>
                    Squash uc' savedExpr initExpr finalExpr uc vExpr 
    -- If it is not self-recursive, then it must be not a constant
    SquashNotSelfRec : SelfDepends initExpr finalExpr False =>
                       Squash uc' savedExpr initExpr finalExpr (S uc') (Undet ? uc')

  public export
  data ResetIndex : {isDet : _} -> {mVTy : _} ->
                    (uc' : Nat) -> (vExpr' : VExpr mVTy isDet) ->
                    Nat -> VExpr mVTy isDet -> Type where
    [search uc' vExpr']
    ResetIndexHit : ResetIndex {isDet=False} {mVTy=Just vTy} uc' vExpr' (S uc') $ Undet vTy uc'
    ResetIndexMiss : ResetIndex {isDet=True} uc v uc v

  public export
  data ValueUnwinding : (uc' : Nat) -> (savedV : Value) -> (g : Guarantee) ->
                        (initV : Value) -> (finalV : Value) ->
                        {-the result uc-}Nat -> {-the result-}Value -> Type where
    [search uc' savedV g initV finalV]
    FinalValueIsPreserved : ValueUnwinding uc savedV SavesValue initV initV uc savedV
    FinalTypeIsPreserved : Squash uc' savedExpr initExpr finalExpr uc vExpr =>
                           ValueUnwinding uc' (V (Just vTy) savedIsDet savedExpr) SavesType (V (Just vTy) initIsDet initExpr) (V (Just vTy) isDet finalExpr) uc $ V (Just vTy) isDet vExpr
    FinalIsIntroduced : ResetIndex uc' vExpr' uc vExpr =>
                        ValueUnwinding uc' _ SavesNothing _ (V (Just vTy) isDet vExpr') uc $ V (Just vTy) isDet vExpr
    -- TODO: maybe I should work differently with completely unknown values or count them properly
    FinalIsUnknown : ValueUnwinding uc savedV SavesNothing (V _ _ _) (V Nothing _ _) uc $ V Nothing False Unkwn

  public export
  data ContUnwinding : (savedCtx : (Nat, VectValue n)) ->
                       (initRegs : VectValue n) -> (gs : Guarantees n) -> (uc : Nat) ->(finalRegs : VectValue n) ->
                       Nat -> VectValue n -> Type where
    [search savedCtx initRegs gs uc finalRegs]
    -- 2 major steps: summarize the iteration and make the new context
    ContUnwindingBase : ContUnwinding (savedUc, []) [] [] uc [] savedUc []
    ContUnwindingStep : ContUnwinding (savedUc, savedRegs') initRegs' g' uc finalRegs' contUc' contRegs' =>
                        ValueUnwinding contUc' savedV vg initV finalV contUc contV =>
                        ContUnwinding (savedUc, savedV :: savedRegs') (initV :: initRegs') (vg :: g') uc (finalV :: finalRegs') contUc (contV :: contRegs') 

  public export
  data IsStrictlyMonotoneVExpr : VExpr (Just I) isDet -> VExpr (Just I) isDet -> Type where
    ItIsInc : IsStrictlyMonotoneVExpr initExpr (Op _ Add initExpr (Det $ RawI 1) @{ovtPrf} @{notAllPrf})
    -- TODO: analyze initExpr and vExpr

  public export
  data HasStrictlyMonotoneValue : VectValue n -> VectValue n -> Type where
    StrictlyMonotoneValueHere : IsStrictlyMonotoneVExpr initExpr finalExpr =>
                                HasStrictlyMonotoneValue ((V (Just I) isDet initExpr) :: initRegs') ((V (Just I) isDet finalExpr) :: finalRegs')
    StrictlyMonotoneValueThere : HasStrictlyMonotoneValue initRegs' finalRegs' =>
                                 HasStrictlyMonotoneValue (v1 :: initRegs') (v2 :: finalRegs')

  public export
  data Edge : (ctx : Context n) -> {-post-}Context n -> Type where
    [search ctx]
    Backward : HasStrictlyMonotoneValue initCtx regs =>
               ContUnwinding savedCtx initCtx g uc regs contUc contRegs => -- context from-loop update happens here
               Concat ls fs contFs =>
               Edge (Ctx ((L savedCtx initCtx g ls) :: ols') uc regs True fs) (Ctx ols' contUc contRegs False contFs)
    Forward : ForwardEdge ctx contCtx -> Edge ctx contCtx

public export
data Program : (ctx : Context n) -> Type where
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
  Sink : {1 ctx, contCtx : _} -> contCtx `IsSankIn` ctx => Program contCtx -> Program ctx

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


test0 : Program {n=2} $ Ctx [] Z [V _ _ (Det $ RawI 1), V _ _ (Det $ RawB True)] True []
test0 = Assign 0 1 $
        Source0 $ 
        Finish

test1 : Program {n=2} $ Ctx [] 1 [V _ _ (Undet _ 0), V _ _ (Det $ RawB True)] True []
test1 = Assign 0 1 $
        Source0 $
        Finish

public export
test2 : Program {n=2} $ Ctx [] 1 [V _ _ (Undet I 0), V _ _ (Det $ RawI 1)] True []
test2 = Source1 @{Forward Free} $
        -- Program {n=2} $ Ctx [] 1 [V _ _ (Undet I 0), V _ _ (Det _ $ RawI 1)] False [(1, [...])]
        Sink @{ItIsSankInWithLoop {g=[SavesType, SavesValue]} @{ItIsSankInViaFree @{JustPick @{PickHit}}} @{GuaranteesType @{GuaranteesValue @{JustGuarantees}}}} $
                                      
        -- After ItIsSankInViaFree
        -- Program {n=2} $ Ctx [] 1 [V _ _ (Undet I 0), V _ _ (Det _ $ RawI 1)] True []
        -- After ItIsSankInWithLoop
        RegOp Add 0 0 1 $
        -- Program {n=2} $ Ctx [L (1, [V I False (Undet I 0), V I True (Det I (RawI 1))])
        --                        [V I False (Undet I 0), V I True (Det I (RawI 1))] 
        --                        [SavesType, SavesValue]
        --                        []
        --                     ] 2 [ V I False (Op 1 Add (Undet I 0) (Det I (RawI 1)))
        --                         , V I True (Det I (RawI 1))
        --                         ] True []
        Source2 @{Backward @{%search} @{ContUnwindingStep @{ContUnwindingStep @{ContUnwindingBase} @{FinalValueIsPreserved}} @{FinalTypeIsPreserved @{SquashSelfRec @{SelfDependsStep}}}}} @{Free} $
        Sink @{ItIsSankInViaFree @{JustPick @{PickHit}}} $
        Source0 $
        Finish

-- TODO: doesn't work if I write "test2' = %search"
test2' : SelfDepends (Undet I 0) (Op 1 Add (Undet I 0) (Det $ RawI 1)) True
test2' = SelfDependsStep @{SelfDependsUndet} @{SelfDependsDet}
