module Spec.Context

import public Spec.Value


%default total


namespace Source
  -- Source is a context at the moment of a jump
  public export
  data Source : Nat -> Type where
    Src : Nat -> VectValue n -> Source n

  public export
  (.undeterminedCount) : Source n -> Nat
  (Src uc regs).undeterminedCount = uc

  public export
  (.registers) : Source n -> VectValue n
  (Src uc regs).registers = regs

  public export
  data ListSource : Nat -> Type where
    Nil : ListSource n
    (::) : Source n -> ListSource n -> ListSource n

  public export
  data Length : (ss : ListSource n) -> Nat -> Type where
    [search ss]
    LengthEmpty : Length [] Z
    LengthNonEmpty : Length ss' l' -> Length (s :: ss') (S l')

  %name Length lenPrf

  public export
  data Index : (i : Fin l) -> (ss : ListSource n) -> Length ss l => Source n -> Type where
    [search i ss]
    IndexBase : Index FZ (s :: ss') @{_} s
    IndexStep : Index i' ss' @{lenPrf'} s -> Index (FS i') (s' :: ss') @{LengthNonEmpty lenPrf'} s

  %name Source.Index indPrf

  public export
  data Concat : (leftSs : ListSource n) -> (rightSs : ListSource n) -> ListSource n -> Type where
    [search leftSs rightSs]
    ConcatBase : Concat [] ss ss
    ConcatStep : Concat {n} ss1' ss2 ss -> Concat {n} (s :: ss1') ss2 (s :: ss)

  public export
  length : ListSource n -> Nat
  length [] = Z
  length (s :: ss') = S $ length ss'

  public export
  index : (i : Fin l) -> (ss : ListSource n) -> Length ss l => Source n
  index i [] @{LengthEmpty} = absurd i
  index FZ (s :: ss') @{LengthNonEmpty _} = s
  index (FS i') (s :: ss') @{LengthNonEmpty _} = index i' ss'

  public export
  (++) : ListSource n -> ListSource n -> ListSource n
  [] ++ ss2 = ss2
  (s :: ss1') ++ ss2 = s :: (ss1' ++ ss2)

  public export
  pick : (i : Fin l) -> (ss : ListSource n) -> Length ss l => (Source n, ListSource n)
  pick i [] @{LengthEmpty} = absurd i
  pick FZ (s :: ss') @{LengthNonEmpty _} = (s, ss')
  pick (FS i') (s :: ss') @{LengthNonEmpty _} = do
    let (recS, recSs) = pick i' ss'
    (recS, s :: recSs)

  public export
  pick' : (ss : ListSource n) -> (i : Fin $ length ss) -> (Source n, ListSource n)
  pick' [] i = absurd i
  pick' (s :: ss') FZ = (s, ss')
  pick' (s :: ss') (FS i') = do
    let (recS, recSs) = pick' ss' i'
    (recS, s :: recSs)

namespace Guarantee
  public export
  data Guarantee = SavesValue | SavesType | SavesNothing

  %name Guarantee g

  -- TODO: or name it ListGuarantee?
  -- TODO: just SavesValue must become (SavesType True)
  public export
  data Guarantees : (n : Nat) -> Type where
    Nil : Guarantees 0
    (::) : Guarantee -> Guarantees n -> Guarantees (S n)

  %name Guarantees gs

  public export
  data IsMet : Guarantee -> Value -> Value -> Type where
    ValueIsMet : IsMet SavesValue (JustV vExpr) (JustV vExpr)
    TypeIsMet : IsMet SavesType (JustV {vTy} vExpr1) (JustV {vTy} vExpr2)

namespace Loop
  public export
  data SavedContext : Nat -> Type where
    SCtx : {-undeterminedCount-}Nat -> {-regs-}VectValue n -> SavedContext n

  public export
  record Loop (n : Nat) where
    constructor L

    savedContext : SavedContext n
    initialContext : VectValue n -- context at the moment of the loop iteration beginning
    contextGuarantees : Guarantees n
    lockedSources : ListSource n

  public export
  data ListLoop : (n : Nat) -> Type where
    Nil : ListLoop n
    (::) : Loop n -> ListLoop n -> ListLoop n

  public export
  length : ListLoop n -> Nat
  length [] = 0
  length (l :: ls') = S $ length ls'

public export
record Context (n : Nat) where
  constructor Ctx

  openLoops : ListLoop n
  undeterminedCount : Nat
  registers : VectValue n
  isInLinearBlock : Bool
  freeSources : ListSource n

%name Context ctx

public export
data Finished : Context n -> Type where
  -- TODO: actually, False can be omitted, but just to be clear for now
  CtxIsFinished : Finished (Ctx [] _ _ False [])

