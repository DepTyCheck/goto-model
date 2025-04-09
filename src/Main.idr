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
import Test.DepTyCheck.Gen.Coverage
import Show.Program.Raw
import Gens.Auto.Derivation.Sink
import Gens.Auto.Derivation.Loop
import Gens.Auto.Derivation.LinearBlock
import Gens.Auto.Derivation.Edge
import Gens.Auto.Derivation.Program
import Main.LabelCollector


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

  ch <- makeChannel {a=Message}
  let cgi = initCoverageInfo'' [`{Program}]
  h <- LabelCollector.start ch cgi

  evalRandomT randomGen $ Data.List.Lazy.for_ (fromList [(S Z)..n]) $ \k => do
    startMoment <- lift $ liftIO $ clockTime clock
    -- test' <- unGenLC h $ genSink (limit f) {n=5} Nothing [Src [JustV (Undet I 0), JustV (Undet I 1), JustV (Det $ RawI 1), JustV (Det $ RawB True), JustV (Undet B 2)]]
    test' <- unGenLC h $ genProgram (limit f) @{genSink} @{genLoopDecision} @{genCloseLoopDecision} @{genLinearBlock} @{genEdgeDecision} {n=5} Nothing Nothing [Src [JustV (Undet I 0), JustV (Undet I 1), JustV (Det $ RawI 1), JustV (Det $ RawB True), JustV (Undet B 2)]] 100 3 []
    finishMoment <- lift $ liftIO $ clockTime clock

    when (k < n) $ LabelCollector.divide h

    let diff = timeDifference finishMoment startMoment
    let diff_str = showTime 5 5 diff

    putStr "Test=\{show k}, time spent=\{diff_str}: "

    case test' of
         (Just test) => do
           putStrLn "Successful\n"
           putStrLn "\{show test}\n"
         Nothing => do
           putStrLn "Failed"

  LabelCollector.stop h


covering
main : IO ()
main = runEitherT {m = IO} run >>= either (die . (++) "Error: ") pure
