module Gens.Manual.Program

import Data.Fuel
import public Spec.Program
import Test.DepTyCheck.Gen

%default total

public export
leftDepth : Fuel -> Nat1
leftDepth = go 1 where
  go : Nat1 -> Fuel -> Nat1
  go n Dry      = n
  go n (More x) = go (succ n) x

public export
genProgram : Fuel ->
             Fuel ->
             (Fuel -> {m, n : _} -> (immSrc : MaybeSource n) -> (srcs : VectSource m n) -> (uc : _) -> Gen MaybeEmpty $ (bs ** curSrc ** l ** remSrcs : VectSource l n ** contUc ** Sink immSrc srcs uc bs curSrc remSrcs contUc)) =>
             (Fuel -> {n : _} -> (regs : VectValue n) -> Gen MaybeEmpty (finalRegs ** LinearBlock regs finalRegs)) =>
             (Fuel -> {n : _} -> {l : _} -> (srcs : VectSource l n) -> (regs : VectValue n) -> Gen MaybeEmpty (r ** contMsrc1 ** contMsrc2 ** contSrcs' : VectSource r n ** Possible srcs regs contMsrc1 contMsrc2 contSrcs')) =>
             {n, m : _} ->
             (immSrc, delaSrc : _) -> (srcs : VectSource m n) -> (uc : _) -> Gen MaybeEmpty $ Program immSrc delaSrc srcs uc []
genProgram f Dry immSrc Nothing [] uc = case immSrc of
                                             Nothing => pure Finish
                                             (Just _) => pure FinishAll
genProgram f Dry immSrc Nothing (src :: srcs) uc = pure FinishAll
genProgram f Dry _ (Just _) srcs uc = empty
genProgram f curF@(More curF') @{genSink} @{genLinearBlock} @{genPossible} immSrc delaSrc srcs uc = do
  let Target : Type; Target = Program immSrc delaSrc srcs uc []

  let stepPath : Gen MaybeEmpty Target; stepPath = do
    (bs ** curSrc ** _ ** remSrcs ** contUc ** sink) <- genSink f immSrc srcs uc
    (finalRegs ** linBlk) <- genLinearBlock f curSrc.registers
    (_ ** contImmSrc ** contDelaSrc ** contSrcs' ** possible) <- genPossible f remSrcs finalRegs
    cont <- genProgram f curF' @{genSink} @{genLinearBlock} @{genPossible} contImmSrc contDelaSrc (snd $ append' delaSrc contSrcs') contUc
    pure $ Step bs @{sink} linBlk @{possible} cont

  let finishAllPath : Gen MaybeEmpty Target; finishAllPath = do
    case delaSrc of
         Nothing => do
           case immSrc of
                Nothing => do
                  case srcs of
                       [] => pure Finish
                       (_ :: _) => pure FinishAll
                (Just _) => pure FinishAll
         (Just _) => empty

  frequency [(5, stepPath), (1, finishAllPath)]

