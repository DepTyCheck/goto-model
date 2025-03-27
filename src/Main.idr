module Main


import Control.Monad.State
import Control.Monad.Either
import Control.Monad.Random

import Data.Fuel
import Data.String
import Data.List.Lazy

import System
import System.Clock
import System.Random.Pure.StdGen

import Test.DepTyCheck.Gen
import Show.Program.Asm
-- import Gens.Auto.Derivation
import Gens.Auto.Derivation.Program
import Gens.Manual.Program


%ambiguity_depth 1003

getNat : HasIO io => io Nat
getNat = stringToNatOrZ <$> getLine

fromVE : {mVTy : _} -> {isDet : _} -> VExpr mVTy isDet -> Value
fromVE vExpr = JustV $ vExpr

covering
run : HasIO io => MonadError String io => io ()
run = do
  n <- getNat
  seed <- cast <$> getNat
  f <- getNat
  let randomGen = mkStdGen seed
  let clock : ?; clock = Monotonic

  evalRandomT randomGen $ Data.List.Lazy.for_ (fromList [(S Z)..n]) $ \k => do
    startMoment <- lift $ liftIO $ clockTime clock
    test' <- unGen' $ genProgram (limit f) (limit f) {n=3} @{genHasTrueBut} @{genLinearBlock} @{genPossible} Nothing Nothing [(Src [fromVE (Undet I 0), fromVE (Undet I 1), fromVE (Det $ RawI 1)])]
    finishMoment <- lift $ liftIO $ clockTime clock

    let diff = timeDifference finishMoment startMoment
    let diff_str = showTime 5 5 diff

    putStr "Test=\{show k}, time spent=\{diff_str}: "

    case test' of
         (Just test) => do
           putStrLn "Successful"
           putStrLn $ show test
         Nothing => do
           putStrLn "Failed"


covering
main : IO ()
main = {-putStr (show test2) -} runEitherT {m = IO} run >>= either (die . (++) "Error: ") pure
