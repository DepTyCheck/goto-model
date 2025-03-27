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
             (Fuel -> {n, m : _} -> (msrc : MaybeSource n) -> Gen MaybeEmpty (bs : VectBool m ** HasTrueBut bs msrc)) =>
             (Fuel -> {n : _} -> (regs : VectValue n) -> Gen MaybeEmpty (finalRegs ** LinearBlock regs finalRegs)) =>
             (Fuel -> {n : _} -> {l : _} -> (srcs : VectSource l n) -> (regs : VectValue n) -> Gen MaybeEmpty (r ** contMsrc1 ** contMsrc2 ** contSrcs' : VectSource r n ** Possible srcs regs contMsrc1 contMsrc2 contSrcs')) =>
             {n, m : _} ->
             (immSrc, delaSrc : _) -> (srcs : VectSource m n) -> Gen MaybeEmpty $ Program immSrc delaSrc srcs
genProgram f Dry immSrc Nothing [] = case immSrc of
                                          Nothing => pure Finish
                                          (Just _) => pure FinishAll
genProgram f Dry _ Nothing (src :: srcs) = pure FinishAll
genProgram f Dry _ (Just _) srcs = empty
genProgram f curF@(More curF') @{genHasTrueBut} @{genLinearBlock} @{genPossible} immSrc delaSrc srcs = do
  let TargetType : Type; TargetType = Program immSrc delaSrc $ srcs

  let stepPath : Gen MaybeEmpty TargetType; stepPath = do
    (bs ** hasTrueBut) <- genHasTrueBut f immSrc
    let extr : ?; extr = extractAtMany bs @{hasTrueBut} (srcs)
    let merged : Source n; merged = merge (snd $ append'' immSrc (snd $ fst extr))
    (finalRegs ** linBlk) <- genLinearBlock f merged.registers
    (_ ** contImmSrc ** contDelaSrc ** contSrcs' ** possible) <- genPossible f (snd $ snd extr) finalRegs
    cont <- genProgram f curF' @{genHasTrueBut} @{genLinearBlock} @{genPossible} contImmSrc contDelaSrc (snd $ append' delaSrc contSrcs')
    pure $ Step bs @{hasTrueBut} linBlk @{possible} cont

  let finishAllPath : Gen MaybeEmpty TargetType; finishAllPath = do
    case delaSrc of
         Nothing => case immSrc of
                         Nothing => case srcs of
                                         [] => empty
                                         (_ :: _) => pure FinishAll
                         (Just _) => pure FinishAll
         (Just _) => empty

  frequency [(5 * (leftDepth curF), stepPath), (1 * (leftDepth curF), finishAllPath)]

