module Gens.Auto.Interface.Program

import public Gens.Auto.Interface.Common
import public Spec.Program


public export
genProgram : Fuel ->
             {m, n : Nat} -> (immSrc : MaybeSource n) -> (delaSrc : MaybeSource n) -> (srcs : VectSource m n) -> (cLim : Nat) -> (uc : Nat) -> (ols : ListLoop n) ->
             Gen MaybeEmpty $ Program immSrc delaSrc srcs cLim uc ols
{-
public export
genSink : Fuel ->
          {m : _} -> {n : _} -> (immSrc : MaybeSource n) -> (srcs : VectSource m n) -> (uc : _) ->
          Gen MaybeEmpty (bs ** curSrc ** l ** remSrcs : VectSource l n ** contUc ** Sink immSrc srcs uc bs curSrc remSrcs contUc)
-- %runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $

public export
genLinearBlock : Fuel ->
                 {n : _} -> (regs : VectValue n) ->
                 Gen MaybeEmpty (finalRegs ** LinearBlock regs finalRegs)

public export
genPossible : Fuel ->
              {n : _} -> {l : _} -> (srcs : VectSource l n) -> (regs : VectValue n) ->
              Gen MaybeEmpty (r ** contImmSrc ** contDelaSrc ** contSrcs : VectSource r n ** Possible srcs regs contImmSrc contDelaSrc contSrcs)

