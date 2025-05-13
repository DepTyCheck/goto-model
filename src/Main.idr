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
import Show.Program.LinearBlock
import Gens.Auto.Derivation
import Main.LabelCollector


%ambiguity_depth 1003

getNat : HasIO io => io Nat
getNat = stringToNatOrZ <$> getLine

{-
l : Loop 5
l = L [ JustV (Undet I 0)
      , JustV (Undet I 1)
      , JustV (Det $ RawI 1)
      , JustV (Det $ RawB True)
      , JustV (Undet B 2)
      ] [] 3 [ GValue
             , GValue
             , GType
             , GNothing
             , GType
             ] [ JustV (Undet I 0)
               , JustV (Undet I 1)
               , JustV (Undet I 2)
               , Unkwn
               , JustV (Undet B 3)
               ] @{TheyAreWinded @{AreWindedStep' @{IsWindedGValue' @{IsWindedUndet'}} $ AreWindedStep' @{IsWindedGValue' @{IsWindedUndet'}} $ AreWindedStep' @{IsWindedGType'} $ AreWindedStep' @{IsWindedGNothing'} $ AreWindedStep' @{IsWindedGType'} $ AreWindedBase'}}
-}

covering
run : HasIO io => MonadError String io => io ()
run = do
  testCount <- getNat
  seed <- cast <$> getNat
  f <- getNat
  cLim <- getNat
  let randomGen = mkStdGen seed
  let clock : ?; clock = Monotonic

  ch <- makeChannel {a=Message}
  let cgi = initCoverageInfo'' [`{Program}]
  h <- LabelCollector.start ch cgi

  evalRandomT randomGen $ Data.List.Lazy.for_ (fromList [(S Z)..testCount]) $ \k => do
    startMoment <- lift $ liftIO $ clockTime clock
    -- test' <- unGenLC h $ genSink (limit f) {n=5} Nothing [Src [JustV (Undet I 0), JustV (Undet I 1), JustV (Det $ RawI 1), JustV (Det $ RawB True), JustV (Undet B 2)]]
    test' <- unGenLC h $ genProgram (limit f) @{genSink} @{genOpenLoopDecision} @{genCloseLoopDecision} @{genLinearBlock} @{genEdgeDecision} {n=5} Nothing Nothing [Src [JustV (Undet I 0), JustV (Undet I 1), JustV (Det $ RawI 1), JustV (Det $ RawB True), JustV (Undet B 2)] Nothing] cLim 3 []
    -- test' <- unGenLC h $ genLinearBlock (limit f) cLim [l] [JustV (Undet I 0), JustV (Undet I 1), JustV (Det $ RawI 1), JustV (Det $ RawB True), JustV (Undet B 2)]
    finishMoment <- lift $ liftIO $ clockTime clock

    when (k < testCount) $ LabelCollector.divide h

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
