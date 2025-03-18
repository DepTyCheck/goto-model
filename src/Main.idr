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
-- import Show.Program
-- import Gens.Auto.Derivation
import Gens.Auto.Derivation.Program


%ambiguity_depth 1003

getNat : HasIO io => io Nat
getNat = stringToNatOrZ <$> getLine

{-

genVExpr01' : Fuel -> (a : _) -> (b : _) -> Gen MaybeEmpty $ VExpr a b
genVExpr01' f a b = genVExpr01 f @{genBoolAnd2} @{genRawValue0} a b

genVExpr0' : Fuel -> (a : _) -> Gen MaybeEmpty (b ** VExpr a b)
genVExpr0' f a = genVExpr0 f @{genVExpr01'} @{genBoolAnd0} @{genRawValue0} a

genVExpr' : Fuel -> Gen MaybeEmpty (a ** b ** VExpr a b)
genVExpr' f = genVExpr f @{genVExpr01'} @{genVExpr0'} @{genBoolAnd0} @{genRawValue0}

genRawValue' : Fuel -> Gen MaybeEmpty (a ** RawValue a)
genRawValue' f = genRawValue f @{genRawValue0}

genValue' : Fuel -> Gen MaybeEmpty Value
genValue' f = genValue f @{genVExpr'}

genProgram' : Fuel -> {n : _} -> (ctx : Context n) -> Gen MaybeEmpty $ Program ctx
genProgram' f ctx = genProgram f @{genBoolAnd012} @{genBoolAnd0} @{genBoolAnd1} @{genBoolAnd2} @{genNotSame01}
                                 @{genRawValue0}
                                 @{genRawValue'}
                                 @{genVExpr01'}
                                 @{genVExpr0'}
                                 @{genVExpr'}
                                 @{genValue'} ctx -}

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
    test' <- unGen' $ genProgram (limit f) (Ctx {n=3} $ Src [fromVE (Undet I 0), fromVE (Undet I 1), fromVE (Det $ RawI 1)]) <&> show
    finishMoment <- lift $ liftIO $ clockTime clock

    let diff = timeDifference finishMoment startMoment
    let diff_str = showTime 5 5 diff

    putStr "Test=\{show k}, time spent=\{diff_str}: "

    case test' of
         (Just test) => do
           putStrLn "Successful"
           -- putStrLn $ test
         Nothing => do
           putStrLn "Failed"


covering
main : IO ()
main = {-putStr (show test2) -} runEitherT {m = IO} run >>= either (die . (++) "Error: ") pure
