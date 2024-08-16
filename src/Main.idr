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
import Gens.Auto.Derivation.Tree
import Gens.Manual.Tree
import Show.Tree

%ambiguity_depth 1003

getNat : HasIO io => io Nat
getNat = stringToNatOrZ <$> getLine

covering
run : HasIO io => MonadError String io => io ()
run = do
  seed <- cast <$> getNat
  f <- getNat
  vc <- getNat
  lc <- getNat
  let randomGen = mkStdGen seed
  let clock : ?; clock = Monotonic

  evalRandomT randomGen $ Data.List.Lazy.for_ (fromList [(S Z)..1000]) $ \k => do
    startMoment <- lift $ liftIO $ clockTime clock
    test' <- unGen' $ genPrimaryTree (limit f) 0 vc lc
    finishMoment <- lift $ liftIO $ clockTime clock

    let diff = timeDifference finishMoment startMoment
    let diff_str = showTime 5 5 diff

    putStr "Test=\{show k}, time spent=\{diff_str}: "

    case test' of
         (Just test) => do
           putStrLn "Successful"
           printLn (render (Opts 1000) $ prettyTree test)
         Nothing => do
           putStrLn "Failed"



covering
main : IO ()
main = runEitherT {m = IO} run >>= either (die . (++) "Error: ") pure
