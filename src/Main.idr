module Main

import Data.Nat
import Data.Fin
import Data.List


%hide List


data SortedNatList : Type
data IsNil : SortedNatList -> Type
data IsSorted : Nat -> SortedNatList -> Type

data SortedNatList : Type where
  Nil : SortedNatList
  (::) : (head : Nat) -> (tail : SortedNatList) -> IsSorted head tail => SortedNatList

data IsNil : SortedNatList -> Type where
  SureNil : IsNil []
  
data IsSorted : (head : Nat) -> (tail : SortedNatList) -> Type where
  EmptySorted : IsSorted h []
  NonEmptySorted : LTE h th => IsSorted th tt => IsSorted h (th :: tt)

data Contains : (sub : SortedNatList) -> (l : SortedNatList) -> Type where
  ContainsEmpty : Contains [] l
  -- TODO: actually can make a hint
  ContainsNonEmptyHit : IsSorted h subt => IsSorted h t => Contains subt t => Contains (h :: subt) (h :: t)
  ContainsNonEmptyMiss : IsSorted subh subt => IsSorted h t => Contains (subh :: subt) t => Contains (subh :: subt) (h :: t)

data AllNatList : (f : Nat -> Type) -> (l : SortedNatList) -> Type where
  [search l]
  AllEmpty : AllNatList f []
  AllNonEmpty : f h => IsSorted h t => AllNatList f t => AllNatList f (h :: t)

data AllLTE : Nat -> SortedNatList -> Type where
  AllLTEAny : AllNatList (\x => LTE a x) l => AllLTE a l

%hint
trans_LTE_LTE : LTE a b -> LTE b c -> LTE a c
trans_LTE_LTE LTEZero y = LTEZero
trans_LTE_LTE (LTESucc x) (LTESucc y) = LTESucc (trans_LTE_LTE x y)

weakenContains : Contains sub l -> IsSorted a l -> Contains sub (a :: l)
weakenContains ContainsEmpty sortedPrf = ContainsEmpty
weakenContains (ContainsNonEmptyHit @{subSortedPrf} @{sortedPrf} @{tailPrf}) supSortedPrf = ContainsNonEmptyMiss
weakenContains (ContainsNonEmptyMiss @{subSortedPrf} @{sortedPrf} @{tailPrf}) supSortedPrf = ContainsNonEmptyMiss

sortedHeadSorted : IsSorted h t => IsSorted a (h :: t) -> LTE a h
sortedHeadSorted (NonEmptySorted @{prf}) = prf

sortedTailSorted : IsSorted h t => IsSorted a (h :: t) -> IsSorted a t
sortedTailSorted (NonEmptySorted @{ltePrf} @{EmptySorted}) = EmptySorted
sortedTailSorted (NonEmptySorted @{ltePrf} @{NonEmptySorted @{ltePrf1}}) = NonEmptySorted @{trans_LTE_LTE ltePrf ltePrf1}

containsImpliesSorted : IsSorted a l -> Contains sub l -> IsSorted a sub
containsImpliesSorted _ ContainsEmpty = EmptySorted
containsImpliesSorted supSortedPrf ContainsNonEmptyHit =
  NonEmptySorted @{sortedHeadSorted supSortedPrf}
containsImpliesSorted supSortedPrf (ContainsNonEmptyMiss @{subSortedPrf} @{sortedPrf} @{tailPrf}) =
  containsImpliesSorted (sortedTailSorted supSortedPrf) tailPrf

containsExpands : (sortedPrf : IsSorted h l) => (prf : Contains sub l) -> Contains ((::) h sub @{containsImpliesSorted sortedPrf prf}) (h :: l)
containsExpands @{sortedPrf} prf = ContainsNonEmptyHit @{containsImpliesSorted sortedPrf prf}

allLTEIdentity : AllLTE a l -> AllNatList (\x => LTE a x) l
allLTEIdentity (AllLTEAny @{prf}) = prf

weakenAllLTELimit : AllLTE (S a) l -> AllLTE a l
weakenAllLTELimit (AllLTEAny @{AllEmpty}) = AllLTEAny
weakenAllLTELimit (AllLTEAny @{AllNonEmpty @{ltePrf} @{sortedPrf} @{tailPrf}}) =
  AllLTEAny @{AllNonEmpty @{lteSuccLeft ltePrf} @{sortedPrf} @{allLTEIdentity . weakenAllLTELimit $ AllLTEAny @{tailPrf}}}

%hint
allLTEImpliesSorted : AllLTE a l -> IsSorted a l
allLTEImpliesSorted (AllLTEAny @{AllEmpty}) = EmptySorted
allLTEImpliesSorted (AllLTEAny @{AllNonEmpty @{ltePrf} @{sortedPrf} @{tailPrf}}) = NonEmptySorted

containsPreservesAllLTE : Contains sub l -> AllLTE a l -> AllLTE a sub
containsPreservesAllLTE ContainsEmpty y = AllLTEAny
-- ContainsNonEmptyHit -> sub is (h :: subt), l is (h :: t)
-- Contains (h :: subt) (h :: t), AllLTE a (h :: t)
-- Contains subt t -> AllLTE a t -> AllLTE a subt
-- need AllLTE a (h :: subt)
containsPreservesAllLTE (ContainsNonEmptyHit @{subSortedPrf} @{_} @{tailContainsPrf}) (AllLTEAny @{AllNonEmpty @{ltePrf} @{_} @{tailAllPrf}}) =
  let tailAllLTEPrf = containsPreservesAllLTE tailContainsPrf (AllLTEAny @{tailAllPrf})
  in AllLTEAny @{AllNonEmpty @{ltePrf} @{subSortedPrf} @{allLTEIdentity tailAllLTEPrf}}
-- ContainsNonEmptyMiss -> sub is (subh :: subt), l is (h :: t)
-- Contains (subh :: subt) t
-- need AllLTE a (subh :: subt)
containsPreservesAllLTE (ContainsNonEmptyMiss @{_} @{_} @{tailContainsPrf}) (AllLTEAny @{AllNonEmpty @{_} @{_} @{tailAllPrf}}) =
  containsPreservesAllLTE tailContainsPrf (AllLTEAny @{tailAllPrf})

concatAllLTEList : {a : Nat} -> AllLTE a l -> AllLTE a (a :: l)
concatAllLTEList {a} (AllLTEAny @{AllEmpty}) = AllLTEAny @{AllNonEmpty @{reflexive}}
concatAllLTEList {a} (AllLTEAny @{AllNonEmpty}) = AllLTEAny @{AllNonEmpty @{reflexive}}

complement : (sub : SortedNatList) -> (l : SortedNatList) -> Contains sub l => (compl : SortedNatList ** Contains compl l)
complement [] l = ([] ** ContainsEmpty)
complement (h :: subt) ((::) h t @{sortedPrf}) @{ContainsNonEmptyHit} =
  let (compl' ** prf') = complement subt t
  in (compl' ** weakenContains prf' sortedPrf)
complement (subh :: sub) ((::) h t @{sortedPrf}) @{ContainsNonEmptyMiss @{_} @{_} @{tailPrf}} =
  let (compl' ** prf') = complement (subh :: sub) t @{tailPrf}
  in ((::) h compl' @{containsImpliesSorted sortedPrf prf'} ** containsExpands prf')

{-
General idea: goTo <-> comeFrom

  ...some code...
  goTo lbl  // place, where we come from to the label 'lbl'. So-called ComeFrom
  ...some code...
lbl:  // place, where we go to. So-called Sink
  a += 5;
  return;

-}

data Program : (comeFroms : SortedNatList) -> (sinkCount : Nat) -> (len : Nat) -> (isCorrect : Bool) ->
               AllLTE len comeFroms => Type where
  Exit : Program [] sinkCount 1 True
  Abort : Program [] sinkCount 1 False
  NoOp : Program comeFroms sinkCount len isCorrect @{weakenAllLTELimit prf} ->  -- continuation
         Program comeFroms sinkCount (S len) isCorrect @{prf}  -- AllLTE (S len) comeFroms
  -- GoTo forward in continuation-passing style
  ComeFrom : Program ((::) len comeFroms @{allLTEImpliesSorted $ weakenAllLTELimit prf}) sinkCount len isCorrect @{concatAllLTEList $ weakenAllLTELimit prf} ->  -- continuation
             Program comeFroms sinkCount (S len) isCorrect @{prf}  -- AllLTE (S len) comeFroms
  -- Sink plays a role of both being the end for GoTo forward and GoTo backward.
  -- In the first case, we choose which ComeFroms lead to the sink
  -- In the second case, GoBack chooses to which Sink it goes
  Sink : (pickedComeFroms : SortedNatList) -> 
         Contains pickedComeFroms comeFroms =>
         Program (fst $ complement pickedComeFroms comeFroms) (S sinkCount) len isCorrect @{containsPreservesAllLTE (snd $ complement pickedComeFroms comeFroms) (weakenAllLTELimit prf)} ->  -- continuation
         -- AllLTE len (complement pickedComeFroms comeFroms)
         -- complement pickedComeFroms comeFroms -> (compl ** Contains compl comeFroms)
         -- AllLTE (S len) comeFroms -> AllLTE len comeFroms -> AllLTE len compl
         Program comeFroms sinkCount (S len) isCorrect @{prf} -- AllLTE (S len) comeFroms
  -- GoTo backward
  GoBack : Fin sinkCount ->
           Program comeFroms sinkCount len isCorrect @{weakenAllLTELimit prf} ->  -- continuation
           Program comeFroms sinkCount (S len) isCorrect @{prf}


test : Program [] 0 6 True
test = ComeFrom $  -- Program [5] 0 5 True
  Sink [5] $  -- Program [] 1 4 True
  ComeFrom $  -- Program [3] 1 3 True
  Sink [3] $  -- Program [] 2 2 True
  GoBack 0 $  -- Program [] 2 1 True
  Exit
{-


main : IO ()
main = do
   printLn "Hello, Idris!"

