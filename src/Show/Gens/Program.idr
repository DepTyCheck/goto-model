module Show.Gens.Program


import Data.Bool.Xor
import Text.PrettyPrint.Bernardy
import Test.DepTyCheck.Gen
import Spec.Tree.Traversal
import Gens.Manual.Numbers


{-
A program consists of the following instructions:
exit;
nop;
label:
condjmp label;
jmp label;

The algorithm of pretty printing (and actually generating) a program is quite simple:
0) Obtain a traversal array of the given tree
1) Split the traversal array into non-empty parts
   Randomly? We can do so at any moment, but it's senseless when there's not exactly 1 edge (which can become jmp or be omitted)
2) Rearrange parts
3) Pretty print each part
4) Combine them in the order by adding jmps
-}
genLabelsHelper : (n : _) -> (m : Nat) -> Gen NonEmpty $ Vect n String
genLabelsHelper 0 m = pure []
genLabelsHelper (S k) m = do
  rec <- genLabelsHelper k (S m)
  pure $ "label_\{show m}" :: rec

genLabels : (n : _) -> Gen NonEmpty $ Vect n String
genLabels n = genLabelsHelper n 0

getLabelInsn : Fin n -> Vect n String -> String
getLabelInsn i labels = do
  let label = index i labels
  label ++ ":"

strengthen' : {n : _} -> (m : Fin (S n)) -> Either (m = Data.Fin.last) (m' : Fin n ** finToNat m = finToNat m')
strengthen' {n = 0} FZ = Left Refl
strengthen' {n = (S k)} FZ = let m' : Fin (S k)
                                 m' = FZ in Right (m' ** Refl)
strengthen' {n = (S k)} (FS x) = let rec = strengthen' x in case rec of
                                                                 (Left lastPrf) => Left $ cong FS lastPrf
                                                                 (Right (m' ** eqPrf)) => Right (FS m' ** cong S eqPrf)

genSplit : {m : _} -> {n' : _} -> let n = S n' in Vect m (TreeTraversalData n) ->
           Gen NonEmpty $ (k : Fin (S n) ** Vect (finToNat k) $ List $ TreeTraversalData n)
genSplit [] = pure (0 ** [])
genSplit (x@(TTD _ _ leftEdge rightEdge) :: xs) = do
  let hasLeftE = leftEdge /= Nothing
  let hasRightE = rightEdge /= Nothing
  recSplit <- genSplit xs
  case recSplit of
       (0 ** []) => pure (FS FZ ** [[x]])
       (FS k' ** (l :: ls)) => case (strengthen' k', hasLeftE `xor` hasRightE) of
                                    (Right (k'' ** prf), True) => pure ((FS $ FS k'') ** rewrite sym prf in ([x] :: l :: ls))
                                    _ => pure (FS k' ** ((x :: l) :: ls))

addIndices' : Vect k (List $ TreeTraversalData n) -> Vect k (Fin m) -> Vect k (Fin m, List $ TreeTraversalData n)
addIndices' [] [] = []
addIndices' (x :: xs) (y :: ys) = (y, x) :: addIndices' xs ys

addIndices : Vect k (List $ TreeTraversalData n) -> Vect k (Fin (S k), List $ TreeTraversalData n)
addIndices xs = addIndices' xs $ (\i => FS i) <$> rewrite sym $ lengthCorrect xs in allFins (length xs)

genShuffle : {n : _} -> Vect n a -> Gen NonEmpty $ Vect n a
genShuffle [] = pure []
genShuffle {n = S k} (x :: xs) = oneOf $ alternativesOf $ do
  xsShuffle <- genShuffle xs
  i <- elements {em = NonEmpty} $ fromList $ Fin.List.allFins (S k)
  pure $ insertAt i x xsShuffle

genShuffle0 : {n : _} -> Vect n a -> Gen NonEmpty $ Vect n a
genShuffle0 [] = pure []
genShuffle0 {n = S k} (x :: xs) = do
  xsShuffle <- genShuffle xs
  pure $ x :: xsShuffle

genNNopsDoc : {opts : _} -> (n : Nat) -> Gen NonEmpty $ Doc opts
genNNopsDoc n = pure $ vsep $ getNNops n
  where
    getNNops : Nat -> List $ Doc opts
    getNNops 0 = []
    getNNops (S k) = "nop;" :: getNNops k

genLinearBlock : {opts : _} -> Gen NonEmpty $ Doc opts
genLinearBlock = do
  let blockLen = 3
  genNNopsDoc blockLen

prettyProgram'' : {n' : _} -> {opts : _} -> {k : _} -> let n = S n' in
                  (Fin (S k), List $ TreeTraversalData n) -> (labelTable : Vect n String) -> Gen NonEmpty $ Doc opts
prettyProgram'' (_, []) labelTable = pure empty
prettyProgram'' (next, (TTD currentIndex _ leftEdge rightEdge) :: xs) labelTable = do
  recDoc <- prettyProgram'' (next, xs) labelTable
  let headBody = vsep [ line $ getLabelInsn currentIndex labelTable
                      , !genLinearBlock
                      ]
  let blockDoc = appendFinish headBody leftEdge rightEdge
  pure $ if length xs == 0
            then blockDoc
            else vappend blockDoc recDoc
  where
    getInsnWithLabel : String -> Fin (S n') -> Doc opts
    getInsnWithLabel x i = Doc.line {opts} "\{x} \{index i labelTable};"

    appendFinish : Doc opts -> MaybeFin (S n') -> MaybeFin (S n') -> Doc opts
    appendFinish d (Just e1) (Just e2) = vappend d $ getInsnWithLabel "condjmp" e2
    appendFinish d (Just e) Nothing = if length xs == 0
                                          then vappend d $ getInsnWithLabel "jmp" e
                                          else d
    appendFinish d Nothing (Just e) = appendFinish d (Just e) Nothing
    appendFinish d Nothing Nothing = vappend d "exit;"

prettyProgram' : {n' : _} -> {opts : _} -> {m : _} -> {k : _} -> let n = S n' in
                 Vect m (Fin (S k), List $ TreeTraversalData n) -> (labelTable : Vect n String) -> Gen NonEmpty $ Doc opts
prettyProgram' [] labelTable = pure empty
prettyProgram' (l :: ls) labelTable = pure $ vappend !(prettyProgram'' {opts} l labelTable) !(prettyProgram' {opts} ls labelTable)

public export
prettyProgram : {opts : _} -> {vc : _} -> {lc : _} ->
                (tree : StrongTree vc lc) -> Gen NonEmpty $ Doc opts
prettyProgram {vc = S vc'} tree = do
  let trArray = buildStdTraversalArray tree 0
  labelTable <- genLabels (S vc')
  (_ ** split) <- genSplit trArray
  let indexedSplit = addIndices split
  shuffledSplit <- genShuffle0 indexedSplit
  prettyProgram' shuffledSplit labelTable

