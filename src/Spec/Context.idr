module Spec.Context

import public Spec.Value


%default total


namespace Source
  -- Source is a context at the moment of a jump
  public export
  data Source : Nat -> Type where
    Src : Nat -> VectValue n -> Source n

  public export
  data ListSource : Nat -> Type where
    Nil : ListSource n
    (::) : Source n -> ListSource n -> ListSource n

  public export
  data Concat : (leftSs : ListSource n) -> (rightSs : ListSource n) -> ListSource n -> Type where
    [search leftSs rightSs]
    ConcatBase : Concat [] ss ss
    ConcatStep : Concat {n} ss1' ss2 ss -> Concat {n} (s :: ss1') ss2 (s :: ss)

  public export
  data Length : (ss : ListSource n) -> Nat -> Type where
    [search ss]
    LengthEmpty : Length [] Z
    LengthNonEmpty : Length ss' l' -> Length (s :: ss') (S l')

  public export
  data Index : (i : Fin l) -> (ss : ListSource n) -> Length ss l => Source n -> Type where
    [search i ss]
    IndexBase : Index FZ (s :: ss') @{_} s
    IndexStep : Index i' ss' @{lenPrf'} s -> Index (FS i') (s' :: ss') @{LengthNonEmpty lenPrf'} s

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
    ValueIsMet : IsMet SavesValue v v
    TypeIsMet : IsMet SavesType (V (Just vTy) _ _) (V (Just vTy) _ _)

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

