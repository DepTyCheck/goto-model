module Data.SortedNatList

import public Data.Nat

data SortedNatList : Type where
  Nil : SortedNatList
  One : Nat -> SortedNatList
  (::) : Nat -> Nat -> SortedNatList -> SortedNatList


test : SortedNatList
test = ?hole_head :: ?hole
