module Main.LabelCollector

import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.Coverage

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Maybe
import System
import System.File.ReadWrite
import System.Signal
import public System.Concurrency

%default total

export
data Message : Type where
  Update : (lbl : Label) -> Message
  Divide : Message
  Close : Message

data Exists' : (forall k . (0 a : k) -> Type) -> Type where
  Evidence' : {0 k : Type} -> {0 a : k} -> {this : forall k . (0 a : k) -> Type} -> this a -> Exists' this

record LabelCollectorST where
  constructor LCST
  chan : Channel Message
  mcoverages : List1 ModelCoverage
  initialCGI : Exists' CoverageGenInfo
  lastUpdates : List Label

printMCov : ModelCoverage -> CoverageGenInfo g -> String
printMCov = show @{Colourful} .: registerCoverage

printCGIs : List1 ModelCoverage -> CoverageGenInfo g -> String
printCGIs mcovs cgi = do
  let (finalCGI, ppMcovs) = runState cgi $ for mcovs $ \mcov => do
    modify $ registerCoverage mcov
    pure $ printMCov mcov cgi
  joinBy "\n" $ (addHeaders $ forget ppMcovs) <+> ["", pad "Total coverage:", "", show @{Colourful} finalCGI]
  where
    pad : String -> String
    pad s = let padding = replicate 50 '-' in padding <+> " \{s} " <+> padding

    addHeaders : List String -> List String
    addHeaders = evalState Z . Prelude.traverse (\ppMcov => do
      n <- get
      put (S n)
      pure $ joinBy "\n" [pad "Coverage \{show n}:", "", ppMcov])

modifyHead : (a -> a) -> List1 a -> List1 a
modifyHead f (head ::: tail) = f head ::: tail

covering
collectorMain : HasIO io => StateT LabelCollectorST io ()
collectorMain = do
  prepareSignalHandling
  collectorLoop
  where
    total
    prepareSignalHandling : StateT LabelCollectorST io ()
    prepareSignalHandling = do
      Right _ <- liftIO $ collectSignal SigINT
        | Left (Error code) => die "Failed to set up a signal handler, error: \{show code}"
      pure ()

    covering
    collectorLoop : StateT LabelCollectorST io ()
    collectorLoop = do
      ch <- gets chan
      msg <- liftIO $ channelGet ch
      case msg of
           (Update l) => do
             modify { mcoverages $= modifyHead ((MkModelCoverage $ singleton l 1) <+>), lastUpdates $= (l ::) }
             collectorLoop'
           Divide => do
             modify { mcoverages $= (neutral :::) . forget, lastUpdates $= const [] }
             collectorLoop'
           Close => close
      where
        total
        close : StateT LabelCollectorST io ()
        close = do
          LCST _ mcovs (Evidence' cgi) lupds <- get
          Right () <- ReadWrite.writeFile "mcov.txt" $ printCGIs (reverse mcovs) cgi
            | Left err => die "Failed to save mcov: \{show err}"
          putStrLn "Success in saving mcov"
          Right () <- ReadWrite.writeFile "last_upds.txt" $ fastUnlines $ show <$> lupds
            | Left err => die "Failed to save last updates: \{show err}"
          exitSuccess

        collectorLoop' : StateT LabelCollectorST io ()
        collectorLoop' = do
          msig <- handleNextCollectedSignal
          case msig of
               (Just _) => close
               Nothing => collectorLoop

export
record Handler where
  constructor MkHandler
  tid : ThreadID
  chan : Channel Message

%name Handler lch

export
HasLabelCollector : (m : Type -> Type) -> Type
HasLabelCollector m = (HasIO m, MonadReader Handler m)

export
put : HasIO m => Handler -> Message -> m ()
put (MkHandler _ chan) = liftIO . channelPut chan

export
update : HasIO m => Handler -> Label -> m ()
update h = put h . Update

export
divide : HasIO m => Handler -> m ()
divide = (flip put) Divide

export
close : HasIO m => Handler -> m ()
close = (flip put) Close

export
start : HasIO io => Channel Message -> CoverageGenInfo g -> io Handler
start ch cgi = do
  -- TODO: is it possible to escape this assert_total?
  tid <- liftIO $ assert_total fork $ evalStateT (LCST ch (neutral ::: []) (Evidence' cgi) []) collectorMain
  pure $ MkHandler tid ch

export
[SendLabelsToCollector] HasLabelCollector m => CanManageLabels m where
  manageLabel l x = (liftIO . (flip channelPut) (Update l) =<< (Handler.chan <$> ask)) >> x

export
unGenLC : MonadRandom m => HasIO m => Handler -> Gen em a -> m $ Maybe a
unGenLC h = runMaybeT . runReaderT h . unGen @{%search} @{%search} @{SendLabelsToCollector} {m = ReaderT Handler $ MaybeT m}

export
stop : HasIO io => Handler -> io ()
stop h@(MkHandler tid _) = do
  close h
  liftIO $ threadWait tid

