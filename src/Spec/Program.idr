module Spec.Program

import public Spec.Context


%default total


public export
data Pick : (ss : ListSource n) ->
            Nat -> VectValue n -> ListSource n -> Type where
  [search ss]
  JustPick : (i : Fin l) -> {ss : ListSource n} -> Length ss l =>
             let res = pick i ss in
             Pick ss (fst res).undeterminedCount (fst res).registers (snd res)


-- It is crucial to erase Ops, because otherwise the further dependency analysis in the unwinding step is crazy
public export
data ValueWinding : (uc : Nat) -> (oldV : Value) -> Nat -> Value -> Type where
  [search uc oldV]
  ResetUndetIndex : ValueWinding uc (JustV $ Undet vTy oldIdx)
                                 (S uc) (JustV $ Undet vTy uc)
  EraseOp : ValueWinding uc (JustV {vTy} $ Op vop vExprL vExprR @{ovtPrf} @{andPrf})
                         (S uc) (JustV $ Undet vTy uc)
  SkipDet : ValueWinding uc (JustV {isDet=True} vExpr)
                         uc (JustV vExpr)

public export
data ContWinding : (regs : VectValue n) -> (gs : Guarantees n) ->
                   Nat -> VectValue n -> Type where
  [search regs gs]
  JustGuarantees : ContWinding [] [] Z []
  GuaranteesValue : ContWinding {n} regs' gs' contUc' contRegs' =>
                    ValueWinding contUc' (JustV vExpr) contUc v =>
                    ContWinding {n=S n} ((JustV vExpr) :: regs') (SavesValue :: gs')
                                contUc (v :: contRegs')
  GuaranteesType : ContWinding {n} regs' gs' contUc' contRegs' =>
                   ContWinding {n=S n} ((JustV {vTy} vExpr) :: regs') (SavesType :: gs')
                               (S contUc') ((JustV $ Undet vTy contUc') :: contRegs')
  GuaranteesNothing : ContWinding {n} regs' gs' contUc contRegs' =>
                      ContWinding {n=S n} (v' :: regs') (SavesNothing :: gs') contUc (Unkwn :: contRegs')

public export
data IsSankIn : {-post-}Context n -> (ctx : Context n) -> Type where
  [search ctx]
  ItIsSankInViaFree : Pick {n} fs contUc contRegs contFs =>
                      Ctx {n} [] contUc contRegs True contFs `IsSankIn` Ctx {n} [] uc regs False fs
  ItIsSankInViaLocked : Pick {n} ls contUc contRegs contLs =>
                        Ctx {n} ((L savedCtx initCtx g contLs) :: ols') contUc contRegs True fs
                        `IsSankIn` Ctx {n} ((L savedCtx initCtx g ls) :: ols') uc regs False fs
  ItIsSankInWithLoop : Ctx {n} [] contUc' contRegs' True contFs'  -- TODO: better loop depth handling
                       `IsSankIn` Ctx {n} [] uc regs False fs =>
                       ContWinding {n} contRegs' gs contUc contRegs =>
                       Ctx {n} ((L (SCtx contUc' contRegs') contRegs gs []) :: []) contUc contRegs True contFs'
                       `IsSankIn` Ctx {n} ols uc regs False fs

public export
data FinishesLinBlk : {-post-}Context n -> (ctx : Context n) -> Type where
  [search ctx]
  ItFinishesLinBlk : (Ctx ols uc regs False fs) `FinishesLinBlk` (Ctx ols uc regs True fs)

public export
data ForwardEdge : (ctx : Context n) -> {-post-}Context n -> Type where
  [search ctx]
  Free : ForwardEdge (Ctx {n} [] uc regs False fs) $
                     Ctx {n} [] uc regs False ((Src uc regs) :: fs)
  Locked : ForwardEdge (Ctx {n} ((L savedCtx initCtx gs ls) :: ols') uc regs False fs) $
                       Ctx {n} ((L savedCtx initCtx gs $ (Src uc regs) :: ls) :: ols') uc regs False fs


public export
data ExprUnwinding : (uc' : Nat) -> (savedExpr : VExpr vTy savedIsDet) ->
                     (initExpr : VExpr vTy initIsDet) -> (finalExpr : VExpr vTy finalIsDet) ->
                     Nat -> VExpr vTy isDet -> Type where
  [search uc' savedExpr initExpr finalExpr]
  ExprUnwindingDet : ExprUnwinding {isDet=True} uc savedExpr initExpr finalExpr uc finalExpr
  ExprUnwindingId : ExprUnwinding {isDet=False} uc savedExpr initExpr initExpr uc savedExpr
  ExprUnwindingOp : ExprUnwinding {isDet=False} uc' savedExpr initExpr (Op _ _ _ @{_} @{_}) (S uc') (Undet ? uc')

public export
data SelfDepends : (initExpr : VExpr vTy initIsDet) -> (finalExpr : VExpr vTy finalIsDet) ->
                   Bool -> Type where
  [search initExpr finalExpr]
  SelfDependsDet : SelfDepends _ (Det _) True
  SelfDependsUndet : SelfDepends (Undet vTy i) (Undet vTy i) True
  SelfDependsFalse : NotSame i j => SelfDepends (Undet vTy i) (Undet vTy j) False
  SelfDependsStep : SelfDepends {initIsDet} initExpr vExprL sdL ->
                    SelfDepends {initIsDet} initExpr vExprR sdR ->
                    BoolAnd sdL sdR sd =>
                    SelfDepends {initIsDet} initExpr (Op _ vExprL vExprR @{ovtPrf} @{andPrf}) sd

public export
data Squash : (uc' : Nat) -> (savedExpr : VExpr vTy savedIsDet) ->
              (initExpr : VExpr vTy initIsDet) -> (finalExpr : VExpr vTy finalIsDet) ->
              Nat -> VExpr vTy isDet -> Type where
  [search uc' savedExpr initExpr finalExpr]
  SquashSelfRec : SelfDepends initExpr finalExpr True =>
                  ExprUnwinding uc' savedExpr initExpr finalExpr uc vExpr =>
                  Squash uc' savedExpr initExpr finalExpr uc vExpr
  -- If it is not self-recursive, then it must be not a constant
  SquashNotSelfRec : SelfDepends initExpr finalExpr False =>
                     Squash uc' savedExpr initExpr finalExpr (S uc') (Undet ? uc')

public export
data ResetIndex : (uc' : Nat) -> (vExpr' : VExpr vTy isDet) ->
                  Nat -> VExpr vTy isDet -> Type where
  [search uc' vExpr']
  ResetIndexDet : ResetIndex {isDet=True} uc v uc v
  ResetIndexUndet : ResetIndex {isDet=False} uc' vExpr' (S uc') $ Undet vTy uc'

public export
data ValueUnwinding : (uc' : Nat) -> (savedV : Value) -> (g : Guarantee) ->
                      (initV : Value) -> (finalV : Value) ->
                      {-the result uc-}Nat -> {-the result-}Value -> Type where
  [search uc' savedV g initV finalV]
  FinalValueIsPreserved : ValueUnwinding uc savedV SavesValue initV initV uc savedV
  FinalTypeIsPreserved : Squash uc' savedExpr initExpr finalExpr uc vExpr =>
                         ValueUnwinding uc' (JustV {vTy} savedExpr) SavesType
                                        (JustV {vTy} initExpr) (JustV {vTy} finalExpr)
                                        uc $ JustV {vTy} vExpr
  FinalIsIntroduced : ResetIndex uc' vExpr' uc vExpr =>
                      ValueUnwinding uc' _ SavesNothing _ (JustV {vTy} vExpr') uc $ JustV {vTy} vExpr
  FinalIsUnknown : ValueUnwinding uc savedV SavesNothing _ Unkwn uc $ Unkwn

public export
data ContUnwinding : (savedCtx : SavedContext n) ->
                     (initRegs : VectValue n) -> (gs : Guarantees n) -> (uc : Nat) ->(finalRegs : VectValue n) ->
                     Nat -> VectValue n -> Type where
  [search savedCtx initRegs gs uc finalRegs]
  ContUnwindingBase : ContUnwinding (SCtx savedUc []) [] [] uc [] savedUc []
  ContUnwindingStep : ContUnwinding {n} (SCtx savedUc savedRegs') initRegs' gs' uc finalRegs' contUc' contRegs' ->
                      ValueUnwinding contUc' savedV g initV finalV contUc contV =>
                      ContUnwinding {n=S n} (SCtx savedUc $ savedV :: savedRegs') (initV :: initRegs')
                                    (g :: gs') uc (finalV :: finalRegs')
                                    contUc (contV :: contRegs')

public export
data IsStrictlyMonotoneVExpr : VExpr I isDet -> VExpr I isDet -> Type where
  ItIsInc : IsStrictlyMonotoneVExpr initExpr (Op Add initExpr (Det $ RawI (S a')) @{ovtPrf} @{andPrf})

-- TODO: analyze initExpr and vExpr
public export
data HasStrictlyMonotoneValue : VectValue n -> VectValue n -> Type where
  StrictlyMonotoneValueHere : IsStrictlyMonotoneVExpr initExpr finalExpr =>
                              HasStrictlyMonotoneValue ((JustV {vTy=I} initExpr) :: initRegs')
                                                       ((JustV {vTy=I} finalExpr) :: finalRegs')
  StrictlyMonotoneValueThere : HasStrictlyMonotoneValue {n} initRegs' finalRegs' =>
                               HasStrictlyMonotoneValue {n=S n} (v1 :: initRegs') (v2 :: finalRegs')


public export
data Edge : (ctx : Context n) -> {-post-}Context n -> Type where
  [search ctx]
  Backward : HasStrictlyMonotoneValue {n} initCtx regs =>
             ContUnwinding {n} savedCtx initCtx gs uc regs contUc contRegs =>
             Edge (Ctx {n} ((L savedCtx initCtx gs ls) :: ols') uc regs False fs)
                  (Ctx {n} ols' contUc contRegs False (ls ++ fs))
  Forward : ForwardEdge {n} ctx contCtx -> Edge {n} ctx contCtx

public export
data Program : (ctx : Context n) -> Type where
  -- Linear Block
  Assign : (target : Fin n) -> (i : Fin n) ->
           Program {n} (Ctx ols uc (duplicate target i regs) True fs) ->
           Program {n} $ Ctx ols uc regs True fs
  RegOp : (vop : ValueOp) -> (target : Fin n) ->
          Produce vop regs contV =>
          Program {n} (Ctx ols uc (replaceAt target contV regs) True fs) ->
          Program {n} $ Ctx ols uc regs True fs

  -- Control Flow
  Sink : {ctx, contCtx : _} -> contCtx `IsSankIn` ctx => Program contCtx -> Program ctx

  Source0 : contCtx `FinishesLinBlk` ctx =>
            Program contCtx ->
            Program ctx
  Source1 : contCtx' `FinishesLinBlk` ctx =>
            Edge contCtx' contCtx =>
            Program {n} contCtx ->
            Program {n} ctx
  Source2 : contCtx'' `FinishesLinBlk` ctx =>
            Edge contCtx'' contCtx' =>
            ForwardEdge contCtx' contCtx =>
            Program {n} contCtx ->
            Program {n} ctx

  Finish : Finished ctx => Program ctx

%name Program prog

test0 : Program {n=2} $ Ctx [] Z [JustV $ Det $ RawI 1, JustV $ Det $ RawB True] True []
test0 = Assign 0 1 $
        Source0 $
        Finish

test1 : Program {n=2} $ Ctx [] 1 [JustV $ Undet I 0, JustV $ Det $ RawI 10] True []
test1 = RegOp Add 0 @{ProduceOp @{HasTypeHere} @{%search} @{HasTypeThere HasTypeHere}} $
        Source0 $
        Finish

public export
test2 : Program {n=2} $ Ctx [] 1 [JustV $ Undet I 0, JustV $ Det $ RawI 1] True []
test2 = Source1 @{%search} @{Forward Free} $
        Sink @{ItIsSankInWithLoop {gs=[SavesType, SavesValue]} @{ItIsSankInViaFree @{JustPick 0}} @{GuaranteesType @{GuaranteesValue @{JustGuarantees}}}} $
        RegOp Add 0 @{ProduceOp @{HasTypeHere} @{%search} @{HasTypeThere HasTypeHere}} $
        Source2 @{ItFinishesLinBlk} @{Backward @{StrictlyMonotoneValueHere} @{ContUnwindingStep @{FinalTypeIsPreserved @{SquashSelfRec}} $ ContUnwindingStep @{FinalValueIsPreserved} $ ContUnwindingBase}} @{Free} $
        Sink @{ItIsSankInViaFree} $
        Source0 $
        Finish

{-
test3 : Program {n=2} $ Ctx [] 1 [V ? ? (Undet I 0), V ? ? (Det $ RawB True)] True []
test3 = Source2 $
        Sink @{ItIsSankInViaFree @{JustPick @{PickHit}}} $
        Assign 0 1 @{JustDup @{%search} @{%search}} $
        Source0 $
        Sink @{ItIsSankInViaFree @{JustPick @{PickHit}}} $
        Assign (FS FZ) 0 @{JustDup @{%search} @{ReplaceThere @{ReplaceHere}}} $
        Source0 $
        Finish
