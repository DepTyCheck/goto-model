module Gens.Manual.Program

import Data.Nat1
import public Data.Fuel
import public Test.DepTyCheck.Gen
import public Spec.Program


%default total

depthLeft : Fuel -> Nat1
depthLeft = depthLeft' 1 where
  depthLeft' : Nat1 -> Fuel -> Nat1
  depthLeft' n Dry = n
  depthLeft' n (More f') = depthLeft' (succ n) f'

{-
genProgram' : Fuel -> Fuel ->
              (genIsSankIn : Fuel -> {n : _} -> (ctx : Context n) -> Gen MaybeEmpty (contCtx ** contCtx `IsSankIn` ctx)) =>
              {n : Nat} -> (ctx : Context n) -> Gen MaybeEmpty $ Program ctx
genProgram' _ _ (Ctx ols uc regs False []) = do
  case ols of
       [] => pure Finish
       (_ :: _) => empty
genProgram' f curF ctx@(Ctx ols uc regs False fs@(_ :: _)) = do
  (contCtx ** prf) <- genIsSankIn f ctx
  cont <- genProgram' f curF contCtx @{genIsSankIn}
  pure $ ?hole $ Sink @{prf} cont
genProgram' f curF (Ctx ols uc regs True fs) = ?genProgram_rhs_2

public export
genProgram : Fuel ->
             {n : Nat} -> (ctx : Context n) -> Gen MaybeEmpty $ Program ctx
