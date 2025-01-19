module Show.Gens.Program

import public Test.DepTyCheck.Gen
import public Text.PrettyPrint.Bernardy
import Control.Monad.State
import Spec.TwC


%default total

record GenState where
  constructor GS



genProgram' : {opts : _} -> TwC c -> StateT GenState (Gen MaybeEmpty) (Doc opts)

public export
genProgram : {opts : _} -> TwC c -> Gen MaybeEmpty (Doc opts)
