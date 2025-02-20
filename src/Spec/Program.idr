module Spec.Program

import public Spec.Context


%default total


public export
data PickHelper : (ss : ListSource n) -> (css : ListSource n) ->
                  Nat -> VectValue n -> ListSource n -> Type where
  [search ss css]
  PickMiss : PickHelper {n} ss' (s :: css) resUc resVs resSs =>
             PickHelper {n} (s :: ss') css resUc resVs resSs
  PickHit : Concat {n} ss' css resSs =>
            PickHelper {n} ((Src uc regs) :: ss') css uc regs resSs

-- TODO: only simple case with 1 picked source covered. There is also
-- complex case with many picked sources and merge of their values.
-- Also, merge may require to introduce new undetermined values
public export
data Pick : (ss : ListSource n) ->
            Nat -> VectValue n -> ListSource n -> Type where
  [search ss]
  JustPick : PickHelper {n} ss [] resUc resVs resSs => Pick {n} ss resUc resVs resSs

-- It is crucial to erase Ops, because otherwise the further dependency analysis in the unwinding step is crazy
public export
data ValueWinding : (uc : Nat) -> (oldV : Value) -> Nat -> Value -> Type where
  [search uc oldV]
  ResetUndetIndex : ValueWinding uc (V (Just vTy) False $ Undet ? oldIdx)
                                (S uc) (V (Just vTy) False $ Undet ? uc)
  EraseOp : ValueWinding uc (V (Just vTy) False $ Op vop vExprL vExprR @{ovtPrf} @{andPrf})
                         (S uc) (V (Just vTy) False $ Undet ? uc)
  SkipDet : ValueWinding uc (V (Just vTy) True vExpr)
                         uc (V (Just vTy) True vExpr)

public export
data ContWinding : (regs : VectValue n) -> (gs : Guarantees n) ->
                   Nat -> VectValue n -> Type where
  [search regs gs]
  JustGuarantees : ContWinding [] [] Z []
  GuaranteesValue : ContWinding {n} regs' gs' contUc' contRegs' =>
                    ValueWinding contUc' (V (Just vTy) isDet vExpr) contUc v =>
                    ContWinding {n=S n} ((V (Just vTy) isDet vExpr) :: regs') (SavesValue :: gs')
                                contUc (v :: contRegs')
  GuaranteesType : ContWinding {n} regs' gs' contUc' contRegs' =>
                   ContWinding {n=S n} ((V (Just vTy) isDet vExpr) :: regs') (SavesType :: gs')
                               (S contUc') ((V (Just vTy) False $ Undet ? contUc') :: contRegs')
  GuaranteesNothing : ContWinding {n} regs' gs' contUc contRegs' =>
                      ContWinding {n=S n} (v' :: regs') (SavesNothing :: gs') contUc ((V Nothing False Unkwn) :: contRegs')

public export
data IsSankIn : {-post-}Context n -> (ctx : Context n) -> Type where
  [search ctx]
  -- TODO: potentially, we can allow to enter a context with loops from the outside
  ItIsSankInViaFree : Pick {n} fs contUc contRegs contFs =>
                      Ctx {n} [] contUc contRegs True contFs `IsSankIn` Ctx {n} [] uc regs False fs
  ItIsSankInViaLocked : Pick {n} ls contUc contRegs contLs =>
                        Ctx {n} ((L savedCtx initCtx g contLs) :: ols') contUc contRegs True fs
                        `IsSankIn` Ctx {n} ((L savedCtx initCtx g ls) :: ols') uc regs False fs
  ItIsSankInWithLoop : Ctx {n} [] contUc' contRegs' True contFs'  -- TODO: better loop depth handling
                       `IsSankIn` Ctx {n} [] uc regs False fs =>
                       -- context to-loop update happens here
                       ContWinding {n} contRegs' gs contUc contRegs =>
                       Ctx {n} ((L (SCtx contUc' contRegs') contRegs gs []) :: []) contUc contRegs True contFs'
                       `IsSankIn` Ctx {n} ols uc regs False fs

public export
data ForwardEdge : (ctx : Context n) -> {-post-}Context n -> Type where
  [search ctx]
  -- When a forward edge is attached in a not linear context,
  -- the edge relates to the last completed linear block
  Free : ForwardEdge (Ctx {n} [] uc regs _ fs) $
                     Ctx {n} [] uc regs False ((Src uc regs) :: fs)
  Locked : ForwardEdge (Ctx {n} ((L savedCtx initCtx g ls) :: ols') uc regs _ fs) $
                       Ctx {n} ((L savedCtx initCtx g $ (Src uc regs) :: ls) :: ols') uc regs False fs


-- TODO: maybe not the same mVTy?
public export
data SelfDepends : (initExpr : VExpr mVTy initIsDet) -> (vExpr : VExpr mVTy isDet) ->
                   Bool -> Type where
  [search initExpr vExpr]
  SelfDependsDet : SelfDepends _ (Det _) True
  SelfDependsUndet : SelfDepends (Undet vTy i) (Undet vTy i) True
  SelfDependsFalse : NotSame i j => SelfDepends (Undet vTy i) (Undet vTy j) False
  SelfDependsStep : SelfDepends {mVTy=Just vTy} {initIsDet} initExpr vExprL sdL =>
                    SelfDepends {mVTy=Just vTy} {initIsDet} initExpr vExprR sdR =>
                    BoolAnd sdL sdR sd =>
                    SelfDepends {mVTy=Just vTy} {initIsDet} initExpr (Op _ vExprL vExprR @{ovtPrf} @{andPrf}) sd

public export
data ExprUnwinding : (uc' : Nat) -> (savedExpr : VExpr mVTy savedIsDet) ->
                     (initExpr : VExpr mVTy initIsDet) -> (finalExpr : VExpr mVTy finalIsDet) ->
                     Nat -> VExpr mVTy isDet -> Type where
  [search uc' savedExpr initExpr finalExpr]
  ExprUnwindingDet : ExprUnwinding {isDet=True} uc savedExpr initExpr finalExpr uc finalExpr
  ExprUnwindingId : ExprUnwinding {isDet=False} uc savedExpr initExpr initExpr uc savedExpr
  ExprUnwindingOp : ExprUnwinding {isDet=False} uc' savedExpr initExpr (Op _ _ _ @{_} @{_}) (S uc') (Undet ? uc')

public export
data Squash : (uc' : Nat) -> (savedExpr : VExpr (Just vTy) savedIsDet) ->
              (initExpr : VExpr (Just vTy) initIsDet) -> (finalExpr : VExpr (Just vTy) finalIsDet) ->
              Nat -> VExpr (Just vTy) isDet -> Type where
  [search uc' savedExpr initExpr finalExpr]
  SquashSelfRec : SelfDepends {mVTy=Just vTy} {initIsDet} {isDet=finalIsDet}
                              initExpr finalExpr True =>
                  ExprUnwinding {mVTy=Just vTy} {savedIsDet} {initIsDet} {finalIsDet} {isDet}
                                uc' savedExpr initExpr finalExpr uc vExpr =>
                  Squash {vTy} {savedIsDet} {initIsDet} {isDet}
                         uc' savedExpr initExpr finalExpr uc vExpr
  -- If it is not self-recursive, then it must be not a constant
  SquashNotSelfRec : SelfDepends {mVTy=Just vTy} {initIsDet} {isDet=finalIsDet}
                                 initExpr finalExpr False =>
                     Squash {vTy} {initIsDet}
                            uc' savedExpr initExpr finalExpr (S uc') (Undet ? uc')

public export
data ResetIndex : {isDet : _} -> {mVTy : _} ->
                  (uc' : Nat) -> (vExpr' : VExpr mVTy isDet) ->
                  Nat -> VExpr mVTy isDet -> Type where
  [search uc' vExpr']
  ResetIndexMiss : ResetIndex {isDet=True} uc v uc v
  ResetIndexHit : ResetIndex {isDet=False} {mVTy=Just vTy} uc' vExpr' (S uc') $ Undet vTy uc'

public export
data ValueUnwinding : (uc' : Nat) -> (savedV : Value) -> (g : Guarantee) ->
                      (initV : Value) -> (finalV : Value) ->
                      {-the result uc-}Nat -> {-the result-}Value -> Type where
  [search uc' savedV g initV finalV]
  FinalValueIsPreserved : ValueUnwinding uc savedV SavesValue initV initV uc savedV
  FinalTypeIsPreserved : Squash {vTy} {savedIsDet} {initIsDet} {isDet}
                                uc' savedExpr initExpr finalExpr uc vExpr =>
                         ValueUnwinding uc' (V (Just vTy) savedIsDet savedExpr) SavesType
                                        (V (Just vTy) initIsDet initExpr) (V (Just vTy) isDet finalExpr)
                                        uc $ V (Just vTy) isDet vExpr
  FinalIsIntroduced : ResetIndex {isDet} {mVTy=Just vTy}
                                 uc' vExpr' uc vExpr =>
                      ValueUnwinding uc' _ SavesNothing _ (V (Just vTy) isDet vExpr') uc $ V (Just vTy) isDet vExpr
  FinalIsUnknown : ValueUnwinding uc savedV SavesNothing (V _ _ _) (V Nothing _ _) uc $ V Nothing False Unkwn

public export
data ContUnwinding : (savedCtx : SavedContext n) ->
                     (initRegs : VectValue n) -> (gs : Guarantees n) -> (uc : Nat) ->(finalRegs : VectValue n) ->
                     Nat -> VectValue n -> Type where
  [search savedCtx initRegs gs uc finalRegs]
  -- 2 major steps: summarize the iteration and make the new context
  ContUnwindingBase : ContUnwinding (SCtx savedUc []) [] [] uc [] savedUc []
  ContUnwindingStep : ContUnwinding {n} (SCtx savedUc savedRegs') initRegs' gs' uc finalRegs' contUc' contRegs' =>
                      ValueUnwinding contUc' savedV g initV finalV contUc contV =>
                      ContUnwinding {n=S n} (SCtx savedUc $ savedV :: savedRegs') (initV :: initRegs')
                                    (g :: gs') uc (finalV :: finalRegs')
                                    contUc (contV :: contRegs')

public export
data IsStrictlyMonotoneVExpr : VExpr (Just I) isDet -> VExpr (Just I) isDet -> Type where
  ItIsInc : IsStrictlyMonotoneVExpr initExpr (Op Add initExpr (Det $ RawI (S a')) @{ovtPrf} @{andPrf})
  -- TODO: analyze initExpr and vExpr

public export
data HasStrictlyMonotoneValue : VectValue n -> VectValue n -> Type where
  StrictlyMonotoneValueHere : IsStrictlyMonotoneVExpr {isDet} initExpr finalExpr =>
                              HasStrictlyMonotoneValue ((V (Just I) isDet initExpr) :: initRegs')
                                                       ((V (Just I) isDet finalExpr) :: finalRegs')
  StrictlyMonotoneValueThere : HasStrictlyMonotoneValue {n} initRegs' finalRegs' =>
                               HasStrictlyMonotoneValue {n=S n} (v1 :: initRegs') (v2 :: finalRegs')

public export
data Edge : (ctx : Context n) -> {-post-}Context n -> Type where
  [search ctx]
  Backward : HasStrictlyMonotoneValue {n} initCtx regs =>
             ContUnwinding {n} savedCtx initCtx gs uc regs contUc contRegs => -- context from-loop update happens here
             Concat {n} ls fs contFs =>
             Edge (Ctx {n} ((L savedCtx initCtx gs ls) :: ols') uc regs True fs)
                  (Ctx {n} ols' contUc contRegs False contFs)
  Forward : ForwardEdge {n} ctx contCtx -> Edge {n} ctx contCtx

public export
data Program : (ctx : Context n) -> Type where
  -- Linear Block
  Assign : (target : Fin n) -> (i : Fin n) ->
           Program {n} (Ctx ols uc (duplicate target i regs) True fs) ->
           Program {n} $ Ctx ols uc regs True fs
  RegOp : (vop : ValueOp) -> (target : Fin n) -> (li : Fin n) -> (ri : Fin n) ->
          Index li regs lv => Index ri regs rv =>
          Produce vop lv rv contV =>
          Program {n} (Ctx ols uc (replaceAt target contV regs) True fs) ->
          Program {n} $ Ctx ols uc regs True fs

  -- Control Flow
  Sink : {ctx, contCtx : _} -> contCtx `IsSankIn` ctx => Program contCtx -> Program ctx

  Source0 : Program {n} (Ctx [] uc regs False fs) ->
            Program {n} $ Ctx [] uc regs True fs
  Source1 : Edge (Ctx ols uc regs True fs)
                 (Ctx contOls contUc contRegs False contFs) =>
            Program {n} (Ctx contOls contUc contRegs False contFs) ->
            Program {n} $ Ctx ols uc regs True fs
  Source2 : Edge (Ctx ols uc regs True fs)
                 (Ctx contOls' contUc' contRegs' False contFs') =>
            ForwardEdge (Ctx contOls' contUc' contRegs' False contFs')
                        (Ctx contOls contUc contRegs False contFs) =>
            Program {n} (Ctx contOls contUc contRegs False contFs) ->
            Program {n} $ Ctx ols uc regs True fs

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
        Sink @{ItIsSankInWithLoop {gs=[SavesType, SavesValue]} @{ItIsSankInViaFree @{JustPick @{PickHit}}} @{GuaranteesType @{GuaranteesValue @{JustGuarantees}}}} $

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
test2' : SelfDepends (Undet I 0) (Op Add (Undet I 0) (Det $ RawI 1)) True
test2' = SelfDependsStep @{SelfDependsUndet} @{SelfDependsDet}
