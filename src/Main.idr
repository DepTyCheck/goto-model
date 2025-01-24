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
import Show.Program
{-import Gens.Auto.Derivation.Program


%ambiguity_depth 1003

getNat : HasIO io => io Nat
getNat = stringToNatOrZ <$> getLine

covering
run : HasIO io => MonadError String io => io ()
run = do
  n <- getNat
  seed <- cast <$> getNat
  f <- getNat
  let randomGen = mkStdGen seed
  let clock : ?; clock = Monotonic

  evalRandomT randomGen $ Data.List.Lazy.for_ (fromList [(S Z)..10]) $ \k => do
    startMoment <- lift $ liftIO $ clockTime clock
    test' <- unGen' $ genProgram (limit f) (Ctx {n=3} [] 2 [V _ _ (Undet I 0), V _ _ (Undet I 1), V _ _ (Det $ RawI 1)] True []) {->>=-} <&> show
    finishMoment <- lift $ liftIO $ clockTime clock

    let diff = timeDifference finishMoment startMoment
    let diff_str = showTime 5 5 diff

    putStr "Test=\{show k}, time spent=\{diff_str}: "

    case test' of
         (Just test) => do
           putStrLn "Successful"
           putStrLn test
         Nothing => do
           putStrLn "Failed" -}


covering
main : IO ()
main = putStr (show test2) -- runEitherT {m = IO} run >>= either (die . (++) "Error: ") pure
