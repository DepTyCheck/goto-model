module Spec.Program.Sink

import public Spec.Context.Source

%default total

public export
data SinkIsValid : (immSrc : MaybeSource n) -> (srcs : VectSource m n) -> (bs : VectBool m) -> Type where
  SinkIsValidWithImmediate : SinkIsValid (Just src) srcs bs
  SinkIsValidWithNothing : HasTrue bs => SinkIsValid Nothing (src :: srcs) bs

namespace Sink
  public export
  record Result (n : Nat) where
    constructor R
    mergedSrc : Source n
    remainedSrcsLen : Nat
    remainedSrcs : VectSource remainedSrcsLen n
    mergedUc : Nat

public export
sink : {n : _} -> (immSrc : MaybeSource n) -> (srcs : VectSource m n) -> (uc : Nat) -> (bs : VectBool m) -> SinkIsValid immSrc srcs bs =>
       Sink.Result n
sink (Just src) srcs uc bs @{SinkIsValidWithImmediate} = do
  let extr : ?; extr = extractAtMany' bs srcs
  let merged : ?; merged = merge (src :: (snd $ fst extr)) uc
  R (fst merged) _ (snd $ snd extr) (snd merged)
sink Nothing (src :: srcs) uc bs @{SinkIsValidWithNothing} = do
  let extr : ?; extr = extractAtMany bs (src :: srcs)
  let merged : ?; merged = merge (snd $ fst extr) uc
  R (fst merged) _ (snd $ snd extr) (snd merged)

