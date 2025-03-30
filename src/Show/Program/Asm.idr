module Show.Program.Asm

import public Spec.Program.Labelled

import Show.Program.LinearBlock
import Control.Monad.State
import Data.Vect
import Data.String

namespace Copypaste
  -- SourceIndex t = Fin t

  public export
  data MaybeSourceIndex : MaybeSource n -> Nat -> Type where
    HasIndex : Fin t -> MaybeSourceIndex (Just src) t
    NoIndex : MaybeSourceIndex Nothing t

  public export
  extractAtManyI' : (bs : VectBool m) -> (srcs: VectSource m n) ->
                    Vect m (Fin fullL) ->
                    (l ** is : Vect l (Fin fullL) ** l = (fst $ snd $ extractAtMany' bs srcs))
  extractAtManyI' [] [] [] = (_ ** [] ** Refl)
  extractAtManyI' (b :: bs) (src :: srcs) (srcI :: srcsI) = do
    let (l ** remSrcsI ** lPrf) = extractAtManyI' bs srcs srcsI
    case b of
         True => (_ ** remSrcsI ** lPrf)
         False => (_ ** srcI :: remSrcsI ** cong S lPrf)

  public export
  extractAtManyI : (bs : VectBool m) -> (hasTrue : HasTrue bs) => (srcs : VectSource m n) ->
                   Vect m (Fin fullL) ->
                   (l ** remSrcsI : Vect l (Fin fullL) ** l = (fst $ snd $ extractAtMany @{hasTrue} bs srcs))
  extractAtManyI (True :: bs) @{Here} (src :: srcs) (srcI :: srcsI) = extractAtManyI' bs srcs srcsI
  extractAtManyI (b :: bs) @{There _} (src :: srcs) (srcI :: srcsI) = do
    let (l ** remSrcsI ** lPrf) = extractAtManyI bs srcs srcsI
    case b of
         True => (l ** remSrcsI ** lPrf)
         False => (_ ** srcI :: remSrcsI ** cong S lPrf)

  public export
  getRemSourcesIndices : {fullL : Nat} ->
                         {immSrc : _} -> {remSrcs : VectSource l n} -> {m : _} ->
                         (bs : VectBool m) -> (srcs : VectSource m n) -> Sink immSrc srcs uc bs curSrc remSrcs contUc =>
                         Vect m (Fin fullL) ->
                         (t ** remSrcsI : Vect t (Fin fullL) ** t = l)
  getRemSourcesIndices {immSrc = Just src} bs srcs @{SinkWithImmediate} srcsI = extractAtManyI' bs srcs srcsI
  getRemSourcesIndices {immSrc = Nothing} (b :: bs) (src :: srcs) @{SinkWithNothing @{hasTrue}} (srcI :: srcsI) =
    extractAtManyI (b :: bs) @{hasTrue} (src :: srcs) (srcI :: srcsI)

  public export
  appendI' : (msrc : MaybeSource n) -> {l : _} -> (srcs : VectSource l n) ->
           MaybeSourceIndex msrc fullL -> Vect l (Fin fullL) ->
           (r ** is : Vect r (Fin fullL) ** r = (fst $ append' msrc srcs))
  appendI' Nothing srcs NoIndex srcsI = (_ ** srcsI ** Refl)
  appendI' (Just src) srcs (HasIndex srcI) srcsI = (_ ** srcI :: srcsI ** Refl)

getContIndices : {fullL : _} ->
                 {remSrcs : VectSource l n} -> {contSrcs : VectSource r n} ->
                 Possible remSrcs finalRegs contImmSrc contDelaSrc contSrcs ->
                 (Vect l $ Fin fullL) -> Fin fullL ->
                 (MaybeSourceIndex contImmSrc fullL, MaybeSourceIndex contDelaSrc fullL, Vect r $ Fin fullL)
getContIndices ItIsPossibleToExit remSrcsI blkI = (NoIndex, NoIndex, remSrcsI)
getContIndices ItIsPossibleToJmp remSrcsI blkI = (NoIndex, NoIndex, blkI :: remSrcsI)
getContIndices ItIsPossibleToCondjmp remSrcsI blkI = (HasIndex blkI, HasIndex blkI, remSrcsI)

maybeUpdateLabel : {fullL : _} ->
                   MaybeSourceIndex msrc fullL -> (blkLbl : String) ->
                   State (Vect fullL String) ()
maybeUpdateLabel (HasIndex i) blkLbl = modify $ \jmpLbls => replaceAt i blkLbl jmpLbls
maybeUpdateLabel NoIndex _ = pure ()

updateLabels : {fullL : _} ->
               Vect m (Fin fullL) -> String ->
               State (Vect fullL String) ()
updateLabels srcsI blkLbl = for_ srcsI $ \i => modify (\jmpLbls => replaceAt i blkLbl jmpLbls)

showJmp : Possible remSrcs finalRegs contImmSrc contDelaSrc contSrcs -> String -> String
showJmp ItIsPossibleToExit jmpLbl = "exit"
showJmp ItIsPossibleToJmp jmpLbl = "jmp \{jmpLbl}"
showJmp ItIsPossibleToCondjmp jmpLbl = "condjmp \{jmpLbl}"


showBlocks' : {fullL : _} ->
              {immSrc, delaSrc : MaybeSource n} -> {m : _} -> {srcs : VectSource m n} ->
              (prog : Program immSrc delaSrc srcs uc ols) ->
              let l : ?; l = blkCount prog in
              l `LTE` fullL =>
              {-labels of blocks from prog-}Vect l String ->
              MaybeSourceIndex immSrc fullL -> MaybeSourceIndex delaSrc fullL -> (Vect m $ Fin fullL) ->
              State ({-labels for jmps in blocks-}Vect fullL String) $ {-Pretty Printed blocks-}Vect l String
showBlocks' (Step {contSrcs'} bs @{sink} linBlk {remSrcs} @{possible} cont) @{ltePrf} (blkLbl :: contLbls) immSrcI delaSrcI srcsI = do
  let contL : ?; contL = blkCount cont

  let (t ** remSrcsI ** tPrf) = getRemSourcesIndices bs srcs @{sink} srcsI
  let (contImmSrcI, contDelaSrcI, contSrcsI') = getContIndices possible (rewrite sym tPrf in remSrcsI) (natToFinLT contL)
  let (j ** contSrcsI ** jPrf) = appendI' delaSrc contSrcs' delaSrcI contSrcsI'

  ppBlks <- showBlocks' cont @{lteSuccLeft ltePrf} contLbls contImmSrcI contDelaSrcI (rewrite sym jPrf in contSrcsI)

  -- Updating values for immSrc and srcs
  maybeUpdateLabel immSrcI blkLbl
  updateLabels srcsI blkLbl

  jmpLbl <- gets $ index (natToFinLT contL)
  let ppBlk : String; ppBlk = joinBy "\n" ["\{blkLbl}:", show linBlk, showJmp possible jmpLbl]
  pure $ ppBlk :: ppBlks
showBlocks' Finish [] _ _ _ = pure []
showBlocks' FinishAll [] _ _ _ = pure []

public export
showBlocks : {src : _} -> (prog : Program Nothing Nothing [src] uc []) -> Vect (blkCount prog) String
showBlocks prog = do
  let l : ?; l = blkCount prog
  evalState (Vect.replicate (S l) "unknown") $ showBlocks' {fullL=S l} prog @{lteSuccRight reflexive} (labelProgram prog) NoIndex NoIndex [natToFinLT @{LTESucc reflexive} l]

isFinishedCorrectly : Program immSrc delaSrc srcs uc ols -> Bool
isFinishedCorrectly (Step _ _ cont) = isFinishedCorrectly cont
isFinishedCorrectly Finish = True
isFinishedCorrectly FinishAll = False

public export
{src : _} -> Show (Program {n = S n'} Nothing Nothing [src] uc []) where
  show prog = do
    let ppBlks : ?; ppBlks = showBlocks prog
    let ppProg = joinBy "\n\n" $ toList ppBlks
    if isFinishedCorrectly prog
       then ppProg
       else joinBy "\n" [ppProg, "(not finished)"]

