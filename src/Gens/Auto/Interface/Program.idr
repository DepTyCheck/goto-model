module Gens.Auto.Interface.Program

import public Gens.Auto.Interface.Common
import public Spec.Program

public export
genHasTrueBut : Fuel ->
                {n, m : _} -> (msrc : MaybeSource n) ->
                Gen MaybeEmpty (bs : VectBool m ** HasTrueBut bs msrc)

public export
genLinearBlock : Fuel ->
                 {n : _} -> (regs : VectValue n) ->
                 Gen MaybeEmpty (finalRegs ** LinearBlock regs finalRegs)

public export
genPossible : Fuel ->
              {n : _} -> {l : _} -> (srcs : VectSource l n) -> (regs : VectValue n) ->
              Gen MaybeEmpty (r ** contImmSrc ** contDelaSrc ** contSrcs : VectSource r n ** Possible srcs regs contImmSrc contDelaSrc contSrcs)

