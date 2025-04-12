module Spec.Program.LinearBlock

import public Spec.Value
import public Spec.Context.Loop

%default total

-- Complexity: O(n + #GValue * n) = O(n^2)
public export
isSuitable : (finalRegs : VectValue n) -> ListLoop n -> Bool
isSuitable finalRegs [] = True
isSuitable finalRegs ((L savedRegs savedSrcs savedUc gs initRegs) :: ols) =
  hasUndet finalRegs && areGuaranteesWeaklyPreserved gs initRegs finalRegs

public export
data LinearBlock : (cLim : Nat) -> (ols : ListLoop n) -> (regs : VectValue n) -> {-finalRegs-}VectValue n -> Type where
  Assign : {0 n : _}
        -> {0 cLim : _}
        -> {0 ols : ListLoop n}
        -> {regs : VectValue n}
        -> {0 finalRegs : VectValue n}
        -> (target, i : Fin n)
        -> NotSame target i  -- 7
        => let contRegs : ?; contRegs = duplicate target i regs in
           So (isSuitable contRegs ols)  -- 8
        => LinearBlock cLim ols contRegs finalRegs  -- 9
        -> LinearBlock cLim ols regs finalRegs
  RegOp : {0 n : _}
       -> {0 cLim : _}
       -> {0 ols : ListLoop n}
       -> {regs : VectValue n}
       -> {v : _}
       -> {0 finalRegs : VectValue n}
       -> (vop : ValueOp) -> (target : Fin n)
       -> Produce vop cLim regs v  -- 8
       => let contRegs : ?; contRegs = replaceAt target v regs in
          So (isSuitable contRegs ols)  -- 9
       => LinearBlock cLim ols contRegs finalRegs  -- 10
       -> LinearBlock cLim ols regs finalRegs
  Finish : LinearBlock cLim ols regs regs

