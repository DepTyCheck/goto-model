module Gens.Manual.Tree.Sequence

import Control.Monad.State
import Data.SnocList
import Test.DepTyCheck.Gen
import Gens.Manual.Numbers
import public Spec.Tree.Sequence

%default total


genMaybeBoundedNat : (a : Nat) -> (b : Nat) -> Gen MaybeEmpty $ Maybe (c : Nat ** (LTE a c, LTE c b))
genMaybeBoundedNat a b with (isLTE a b)
  genMaybeBoundedNat a b | (Yes prf) = pure $ Just !(genBoundedNat a b)
  genMaybeBoundedNat a b | (No contra) = pure Nothing


genDAG' : {n, m' : _} ->
          let m = S m' in
          Vect n (VertexData m) ->
          Gen MaybeEmpty $ VertexSequence n m
genDAG' [] = pure []
genDAG' (v@(GD index leftEdge rightEdge) :: vs) = do
  rec <- genDAG' vs

  let genEdge : Gen MaybeEmpty (MaybeFin (S m'))
      genEdge = genMaybeBoundedNat (S $ finToNat index) m' >>=
                (\x => case x of
                            Nothing => pure Nothing
                            Just (c ** (_, prf)) => pure $ Just $ natToFinLT c @{LTESucc prf})

  case (leftEdge, rightEdge) of
       (Just _, Nothing) => pure $ (GD index leftEdge !genEdge) :: rec
       (Nothing, Just _) => pure $ (GD index !genEdge rightEdge) :: rec
       (_, _) => pure $ v :: rec

succRepresentation : {n : _} -> IsSucc n -> (n' ** n = S n')
succRepresentation {n = S n'} ItIsSucc = (n' ** Refl)

genDAG : (atree : AbstractTree (Prms n1c n2c lc 0)) ->
         let n = size atree in
         Gen MaybeEmpty $ VertexSequence n n
genDAG atree = do
  let agraph = toAbstractGraph atree
  let (n' ** prf) = succRepresentation $ sizeIsSucc atree
  (rewrite prf in genDAG' (rewrite sym prf in agraph))


-- index for SnocList
xedni : (n : Nat) -> (sx : SnocList a) -> InBounds n sx => a
xedni 0 (sx :< x) @{InFirst} = x
xedni (S k) (sx :< x) @{(InLater boundsPrf')} = xedni k sx @{boundsPrf'}

finIsInBounds : (sx : SnocList a) -> (n : Fin (length sx)) -> InBounds (finToNat n) sx
finIsInBounds [<] n = absurd n
finIsInBounds (sx :< x) FZ = InFirst
finIsInBounds (sx :< x) (FS n') = InLater (finIsInBounds sx n')


record DFSState (totalN : Nat) where
  constructor MkDFSState

  parents : SnocList $ Fin totalN
  

DFSGen : Nat -> Type -> Type
DFSGen m = StateT (SnocList $ Fin m) $ Gen MaybeEmpty

genDTC' : VertexSequence n m ->
          DFSGen m $ VertexSequence n m
genDTC' [] = pure []
genDTC' (v@(GD index leftEdge rightEdge) :: vs) = do
  parents <- removeNotParents <$> get
  put $ parents :< index
  rec <- genDTC' vs
  -- now state is something after recursion, so we must use parents

  let genEdge : MaybeFin m -> Gen MaybeEmpty (MaybeFin m)
      genEdge edge = case edge of
                          Just _ => pure edge
                          Nothing => do
                            parentsIndex <- genFin (length parents)
                            let parentsIndexN : ?; parentsIndexN = finToNat parentsIndex
                            let parentIndex = xedni parentsIndexN parents @{finIsInBounds parents parentsIndex}
                            pure $ Just parentIndex

  pure $ (GD index !(lift $ genEdge leftEdge) !(lift $ genEdge rightEdge)) :: rec
  where
    removeNotParents : SnocList (Fin m) -> SnocList (Fin m)
    removeNotParents [<] = [<]
    removeNotParents (sx :< x) = if (finToNat x) < (finToNat index)
                                    then sx :< x
                                    else removeNotParents sx

-- DTC - Directed Tree with Cycles
genDTC : (atree : AbstractTree (Prms n1c n2c lc 0)) ->
         let n = size atree in
         Gen MaybeEmpty $ VertexSequence n n
genDTC atree = do
  let agraph = toAbstractGraph atree
  let (n' ** prf) = succRepresentation $ sizeIsSucc atree
  evalStateT [<] $ genDTC' agraph

