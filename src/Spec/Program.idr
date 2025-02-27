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

public export
data IsSankIn : {-post-}Context n -> (ctx : Context n) -> Type where
  [search ctx]
  ItIsSankInViaFree : Pick {n} fs contUc contRegs contFs =>
                      Ctx {n} [] contUc contRegs True contFs `IsSankIn` Ctx {n} [] uc regs False fs

public export
data FinishesLinBlk : {-post-}Context n -> (ctx : Context n) -> Type where
  [search ctx]
  ItFinishedLinBlk : (Ctx ols uc regs False fs) `FinishesLinBlk` (Ctx ols uc regs True fs)

public export
data ForwardEdge : (ctx : Context n) -> {-post-}Context n -> Type where
  [search ctx]
  Free : ForwardEdge (Ctx {n} [] uc regs False fs) $
                     Ctx {n} [] uc regs False ((Src uc regs) :: fs)

public export
data Program : (ctx : Context n) -> Type where
  -- Linear Block
  Assign : (target : Fin n) -> (i : Fin n) ->
           -- Duplicate target i regs contRegs =>
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
            ForwardEdge contCtx' contCtx =>
            Program {n} contCtx ->
            Program {n} ctx
  Source2 : contCtx'' `FinishesLinBlk` ctx =>
            ForwardEdge contCtx'' contCtx' =>
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
