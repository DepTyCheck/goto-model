module Spec.Program.LinearBlock

import public Spec.Value

%default total

public export
data LinearBlock : (cLim : Nat) -> (regs : VectValue n) -> {-finalRegs-}VectValue n -> Type where
  Assign : (target, i : Fin n)
        -> NotSame target i
        => LinearBlock cLim (duplicate target i regs) finalRegs
        -> LinearBlock cLim regs finalRegs
  RegOp : (vop : ValueOp) -> (target : Fin n)
       -> Produce vop cLim regs v
       => LinearBlock cLim (replaceAt target v regs) finalRegs
       -> LinearBlock cLim regs finalRegs
  Finish : LinearBlock cLim regs regs

