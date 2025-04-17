module Gens.Auto.Derivation.Program.Loop.Close

import public Gens.Auto.Derivation.Common
import public Gens.Auto.Interface.Program.Loop.Close

%logging "deptycheck.derive" 20

GenOrderTuning "AreWindedStep'".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [11, 10]

GenOrderTuning "CanUnwindAllStep".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [8, 7]

{-
GenOrderTuning "DoClose".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [11, 12, 13, 14]
  -}

Gens.Auto.Interface.Program.Loop.Close.genCloseLoopDecision = deriveGen

