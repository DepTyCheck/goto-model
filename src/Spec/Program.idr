module Spec.Program

import public Spec.Context

%default total

namespace LinearBlock
  public export
  data LinearBlock : VectValue n -> VectValue n -> Type where
    Assign : (target, i : Fin n) ->
             NotSame target i =>
             LinearBlock (duplicate target i regs) finalRegs ->
             LinearBlock regs finalRegs
    RegOp : (vop : ValueOp) -> (target : Fin n) ->
            Produce vop regs v =>
            LinearBlock (replaceAt target v regs) finalRegs ->
            LinearBlock regs finalRegs
    Finish : LinearBlock regs regs

namespace Possible
  public export
  data IsUndet : Fin n -> VectValue n -> Type where
    Here : IsUndet 0 (JustV {vTy} {isDet=False} _ :: vs)
    There : IsUndet idx' vs -> IsUndet (FS idx') (v :: vs)
  
  public export
  data Possible : (remSrcs : VectSource l n) -> (finalRegs : VectValue n) ->
                  MaybeSource n -> MaybeSource n -> VectSource r n -> Type where
    ItIsPossibleToExit : Possible srcs regs Nothing Nothing srcs
    ItIsPossibleToJmp : Possible srcs regs Nothing Nothing (Src regs :: srcs)
    ItIsPossibleToCondjmp : IsUndet i regs => Possible srcs regs (Just $ Src regs) (Just $ Src regs) srcs

-- immediate source - is always taken
-- delayed source - is always avoided for 1 step
-- immediate source is useful because I'll be able to control loops later
-- another reason is that I wish to guarantee 1 further block doesn't get 2 edges from a block before
-- thus, with immediate source I also need a delayed one
-- just delayed isn't enough because it doesn't force the generator to choose the other source
public export
data Program : (immSrc : MaybeSource n) -> (delaSrc : MaybeSource n) -> (srcs : VectSource m n) -> (uc : Nat) -> Type where
  Step : {n : _} -> {srcs : VectSource m n} -> {uc : _} ->
         {finalRegs : VectValue n} ->
         {l : _} -> {contSrcs' : VectSource l n} -> {immSrc, delaSrc, contImmSrc, contDelaSrc : _} ->
         (bs : VectBool m) ->
         (hasTrueBut : HasTrueBut bs immSrc) =>  -- if no immSrc, then must have any True bit
         let extr : ((k' ** VectSource (S k') n), (l ** VectSource l n)); extr = extractAtMany bs @{hasTrueBut} srcs in
         let merged : (Source n, Nat); merged = merge (snd $ append'' immSrc (snd $ fst extr)) uc in
         LinearBlock (fst merged).registers finalRegs ->
         Possible (snd $ snd extr) finalRegs contImmSrc contDelaSrc contSrcs' =>
         Program contImmSrc contDelaSrc (snd $ append' delaSrc contSrcs') (snd merged) ->
         Program immSrc delaSrc srcs uc
  Finish : Program Nothing Nothing [] uc
  FinishAll : HasOneSource immSrc srcs => Program immSrc Nothing srcs uc

test : Program {n=2} (Just $ Src [JustV $ Undet I 0, JustV $ Det $ RawI 1]) Nothing [] 0
test = Step [] (Assign 0 1 $ Finish) Finish

test1 : Program {n=3} (Just $ Src [JustV $ Undet I 0, JustV $ Undet I 1, JustV $ Det $ RawI 1]) Nothing [] 0
test1 = Step [] (Assign 0 1 $ Finish) Finish

