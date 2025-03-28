module Spec.Context

import public Spec.Value
import public Control.Monad.State

%default total

namespace Source
  public export
  data Source : Nat -> Type where
    Src : VectValue n -> Source n

  %name Source src

  public export
  (.registers) : Source n -> VectValue n
  (.registers) (Src vs) = vs

  public export
  data MaybeSource : Nat -> Type where
    Nothing : MaybeSource n
    Just : Source n -> MaybeSource n

  public export
  data VectSource : Nat -> Nat -> Type where
    Nil : VectSource 0 n
    (::) : Source n -> VectSource m n -> VectSource (S m) n

  %name VectSource srcs

  public export
  foldr : (Source n -> acc -> acc) -> acc -> VectSource m n -> acc
  foldr f x [] = x
  foldr f x (src :: srcs) = f src (foldr f x srcs)

  public export
  data HasOneSource : MaybeSource n -> VectSource m n -> Type where
    HasImmSrc : HasOneSource (Just _) srcs
    HasOneSrc : HasOneSource msrc (src :: srcs)

namespace Bool
  public export
  data HasTrueBut : VectBool n -> MaybeSource m -> Type where
    HasTrueSure : HasTrue bs => HasTrueBut bs Nothing
    HasTrueMaybe : HasTrueBut bs (Just _)

namespace Source
  public export
  append' : MaybeSource n -> {l : _} -> VectSource l n -> (r ** VectSource r n)
  append' Nothing srcs = (_ ** srcs)
  append' (Just src) srcs = (_ ** src :: srcs)

  public export
  append'' : MaybeSource n -> {l : _} -> VectSource (S l) n -> (r ** VectSource (S r) n)
  append'' Nothing srcs = (_ ** srcs)
  append'' (Just src) srcs = (_ ** src :: srcs)

  public export
  extractAt : (idx : Fin $ S m) -> VectSource (S m) n -> (Source n, VectSource m n)
  extractAt _ (src :: []) = (src, [])
  extractAt FZ (src :: src1 :: srcs) = (src, src1 :: srcs)
  extractAt (FS idx') (src :: src1 :: srcs) = let (extracted, rem) = extractAt idx' (src1 :: srcs) in (extracted, src :: rem)

  public export
  extractAtMany' : (bs : VectBool m) -> VectSource m n -> ((k ** VectSource k n), (l ** VectSource l n))
  extractAtMany' [] [] = ((0 ** []), (0 ** []))
  extractAtMany' (b :: bs) (src :: srcs) = do
    let rec : ?; rec = extractAtMany' bs srcs
    -- TODO: (extracted, rem) = is broken, terrible syntax :(
    let extracted : ?; extracted = fst rec
    let rem : ?; rem = snd rec
    case b of
         True => ((_ ** src :: snd extracted), rem)
         False => (extracted, (_ ** src :: snd rem))

  public export
  extractAtMany : (bs : VectBool m) -> {msrc : MaybeSource n} -> HasTrueBut bs msrc => VectSource m n -> ((k' ** VectSource (S k') n), (l ** VectSource l n))
  extractAtMany [] {msrc = Nothing} @{HasTrueSure @{hasTrue}} [] = void $ lemma hasTrue
  where
    lemma : HasTrue [] -> Void
    lemma _ impossible
  -- TODO: cannot simply pattern match on hasTrue
  extractAtMany (b :: bs) {msrc = Nothing} @{HasTrueSure @{hasTrue}} (src :: srcs) with (hasTrue)
    extractAtMany (True :: bs) {msrc = Nothing} @{HasTrueSure @{hasTrue}} (src :: srcs) | Here = do
      let rec : ?; rec = extractAtMany' bs srcs
      let extracted : ?; extracted = fst rec
      let rem : ?; rem = snd rec
      ((_ ** src :: snd extracted), rem)
    extractAtMany (True :: bs) {msrc = Nothing} @{HasTrueSure @{hasTrue}} (src :: srcs) | (There hasTrue') = do
      let rec : ?; rec = extractAtMany bs @{HasTrueSure} srcs
      let extracted : ?; extracted = fst rec
      let rem : ?; rem = snd rec
      ((_ ** src :: snd extracted), rem)
    extractAtMany (False :: bs) {msrc = Nothing} @{HasTrueSure @{hasTrue}} (src :: srcs) | (There hasTrue') = do
      let rec : ?; rec = extractAtMany bs @{HasTrueSure} srcs
      let extracted : ?; extracted = fst rec
      let rem : ?; rem = snd rec
      (extracted, (_ ** src :: snd rem))
  extractAtMany bs {msrc = Just src} @{HasTrueMaybe} srcs = do
    let rec : ?; rec = extractAtMany' bs srcs
    let extracted : ?; extracted = fst rec
    let rem : ?; rem = snd rec
    ((_ ** src :: snd extracted), rem)


  -- the Program starts from 1 point
  -- this point fixates undetermined values
  -- after that, I work with these initial values
  -- I can remove any of them
  -- can I introduce any? No during usual instruction, but during merge - yes
  -- I must store the global count of undetermined values in order to save myself from sudden index conflicts
  -- This value must be used during every merge. Thankfully, the program is built linearly
  -- Then, what happens in a loop?
  -- loop may make many iterations
  -- after a loop we do similar things as in merge. Thus, during unwind we use the same global value to introduce changed undetermined values.
  -- If we can, we just change the expressions using the same undet values from saved context

{-
  public export
  mergeStep : Nat -> VectSource (S k') (S n) -> (Nat, Value, VectSource (S k') n)
  mergeStep uc ((Src $ Unkwn :: vs) :: []) = (uc, Unkwn, [Src vs])
  mergeStep uc ((Src $ (JustV {vTy} {isDet = False} vExpr) :: vs) :: []) = (S uc, JustV $ Undet vTy uc, [Src vs])
  mergeStep uc ((Src $ v@(JustV {isDet = True} vExpr) :: vs) :: []) = (uc, v, [Src vs])
  mergeStep uc ((Src $ v :: vs) :: src1 :: srcs) = do
    let (_, merged, rest) = mergeStep 0 (src1 :: srcs)
    let (uc1, v1) = mergeValues uc v merged
    (uc1, v1, Src vs :: rest)
  where
    mergeValues : Nat -> Value -> Value -> (Nat, Value)
    mergeValues uc Unkwn v2 = (uc, Unkwn)
    mergeValues uc (JustV vExpr) Unkwn = (uc, Unkwn)
    mergeValues uc (JustV {vTy=vTy1} {isDet=isDet1} vExpr1) (JustV {vTy=vTy2} {isDet=isDet2} vExpr2) with (decEq vTy1 vTy2, decEq isDet1 isDet2)
      mergeValues uc (JustV {vTy} {isDet} vExpr1) (JustV {vTy} {isDet} vExpr2) | (Yes Refl, Yes Refl) =
        case decEq vExpr1 vExpr2 of
             (Yes Refl) => if isDet
                              then (uc, JustV vExpr1)
                              else (S uc, JustV $ Undet vTy uc)
             (No _) => (S uc, JustV $ Undet vTy uc)
      mergeValues uc (JustV {vTy} {isDet=isDet1} vExpr1) (JustV {vTy} {isDet=isDet2} vExpr2) | (Yes Refl, No _) = (S uc, JustV $ Undet vTy uc)
      mergeValues uc (JustV {vTy=vTy1} {isDet=isDet1} vExpr1) (JustV {vTy=vTy2} {isDet=isDet2} vExpr2) | (No _, _) = (uc, Unkwn)

  public export
  merge' : {n : _} -> Nat -> VectSource (S k') n -> (Nat, Source n)
  merge' {n=Z} _ _ = (0, Src [])
  merge' {n=S n'} uc (src :: srcs) = do
    let (uc1, mergedZero, rest) = mergeStep uc (src :: srcs)
    let (uc2, Src regs') = merge' uc1 rest
    (uc2, Src $ mergedZero :: regs')

-}
  public export
  erase : VType -> StateT Bool (State Nat) Value
  erase vTy = do
    uc <- lift get
    put True
    lift $ put (S uc)
    pure $ JustV $ Undet vTy uc

  public export
  mergeValues : Value -> Value -> Nat -> StateT {-isErased-}Bool (State Nat) Value
  mergeValues Unkwn v2 uc = do
    lift $ put uc  -- reset uc in state back no matter what is v2
    pure Unkwn
  mergeValues (JustV vExpr) Unkwn uc = do
    -- uc is already reset
    pure Unkwn
  mergeValues (JustV {vTy=vTy1} {isDet=isDet1} vExpr1) (JustV {vTy=vTy2} {isDet=isDet2} vExpr2) uc with (decEq vTy1 vTy2, decEq isDet1 isDet2)
    mergeValues (JustV {vTy} {isDet} vExpr1) (JustV {vTy} {isDet} vExpr2) uc | (Yes Refl, Yes Refl) =
      case decEq vExpr1 vExpr2 of
           (Yes Refl) => pure $ JustV vExpr1
           (No _) => do
             if isDet
                then erase vTy  -- if isErased then isDet == False
                else do
                  isErased <- get
                  if isErased
                     then pure $ JustV vExpr2
                     else erase vTy
    mergeValues (JustV {vTy} {isDet=isDet1} vExpr1) (JustV {vTy} {isDet=isDet2} vExpr2) uc | (Yes Refl, No _) = do
      isErased <- get
      if isErased
         then pure $ JustV vExpr2
         else erase vTy
    mergeValues (JustV {vTy=vTy1} {isDet=isDet1} vExpr1) (JustV {vTy=vTy2} {isDet=isDet2} vExpr2) uc | (No _, _) = do
      lift $ put uc  -- reset uc in state
      pure Unkwn

  public export
  mergeStep' : VectSource (S k') (S n) -> StateT Bool (State Nat) (Value, VectSource (S k') n)
  mergeStep' [Src (v :: vs)] = pure (v, [Src vs])
  mergeStep' ((Src (v :: vs)) :: (src :: srcs)) = do
    uc <- lift get
    (merged', rest) <- mergeStep' (src :: srcs)
    merged <- mergeValues v merged' uc
    pure (merged, Src vs :: rest)

  public export
  mergeStep : VectSource (S k') (S n) -> State Nat (Value, VectSource (S k') n)
  mergeStep srcs = evalStateT False $ mergeStep' srcs

  public export
  merge' : {n : _} -> VectSource (S k') n -> State Nat $ Source n
  merge' {n = Z} srcs = pure $ Src []
  merge' {n = S n'} (src :: srcs) = do
    (mergedZero, rest) <- mergeStep (src :: srcs)
    Src mergedRest <- merge' rest
    pure $ Src $ mergedZero :: mergedRest

  public export
  merge : {n : _} -> VectSource (S k') n -> (uc : Nat) -> (Source n, Nat)
  merge srcs uc = swap $ runState uc $ merge' srcs

{-

namespace Loop
  namespace Guarantee
    public export
    data Guarantee = GValue | GType | GNothing
  
    public export
    data VectGuarantee : Nat -> Type where
      Nil : VectGuarantee 0
      (::) : Guarantee -> VectGuarantee n -> VectGuarantee (S n)

    public export
    data IsWindedWithGValue' : Value -> Value -> Nat -> Nat -> Type where
      IsWindedUndet' : IsWindedWithGValue' (JustV {vTy} {isDet = False} vExpr) (JustV $ Undet vTy uc) uc (S uc)
      IsWindedDet' : IsWindedWithGValue' (JustV {isDet = True} vExpr) (JustV vExpr) uc uc


    public export
    data IsWinded' : Value -> Guarantee -> Value -> Nat -> Nat -> Type where
      -- TODO: will probably cause strange filtration
      IsWindedGValue' : IsWindedWithGValue' sr ir uc uc' => IsWinded' sr GValue ir uc uc'
      -- TODO: constants may also be not saved completely
      IsWindedGType' : IsWinded' (JustV {vTy} {isDet = False} vExpr) GType (JustV $ Undet vTy uc) uc (S uc)
      IsWindedGNothing' : IsWinded' v GNothing Unkwn uc uc

    public export
    data AreWinded' : VectValue n -> VectGuarantee n -> VectValue n -> Nat -> Type where
      AreWindedBase' : AreWinded' [] [] [] uc
      AreWindedStep' : AreWinded' savedRegs gs initRegs uc' ->
                       IsWinded' sr g ir uc uc' =>
                       AreWinded' (sr :: savedRegs) (g :: gs) (ir :: initRegs) uc

    public export
    data AreWinded : VectValue n -> VectGuarantee n -> VectValue n -> Type where
      TheyAreWinded : AreWinded' savedRegs gs initRegs 0 => AreWinded savedRegs gs initRegs

    -- TODO: causes fake filtration. CanUnwind must be built upon IsWinded',
    -- but Idris cannot handle it and further usage causes fighting with compiler bugs
    public export
    data CanUnwind : (ir : Value) -> Guarantee -> (fr : Value) -> Type where
      CanUnwindGValue : CanUnwind ir GValue ir
      CanUnwindGType : CanUnwind (JustV {vTy} initExpr) GType (JustV {vTy} finalExpr)
      CanUnwindGNothing : CanUnwind Unkwn GNothing fr

    public export
    data CanUnwindAll : (initRegs : VectValue n) -> (gs : VectGuarantee n) -> (finalRegs : VectValue n) -> Type where
      CanUnwindAllBase : CanUnwindAll [] [] []
      CanUnwindAllStep : CanUnwindAll initRegs gs finalRegs ->
                         CanUnwind ir g fr =>
                         CanUnwindAll (ir :: initRegs) (g :: gs) (fr :: finalRegs)

  public export
  data Loop : Nat -> Type where
    L : (savedRegs : VectValue n) -> (gs : VectGuarantee n) -> (initRegs : VectValue n) ->
        AreWinded savedRegs gs initRegs =>
        Loop n

  %name Loop l

  public export
  data ListLoop : Nat -> Type where
    Nil : ListLoop n
    (::) : Loop n -> ListLoop n -> ListLoop n

  {-
  -- TODO: Nat in state is from saved context!
  public export
  unwind' : {n : _} ->
            (savedRegs : _) -> (gs : _) -> (initRegs, finalRegs : _) ->
            AreWinded' {n} savedRegs gs initRegs uc => CanUnwindAll {n} initRegs gs finalRegs =>
            State Nat $ VectValue n
  unwind' [] [] [] [] @{AreWindedBase'} @{CanUnwindAllBase} = pure []
  unwind' ((JustV vExpr) :: savedRegs) (GValue :: gs) ((JustV $ Undet vTy uc) :: initRegs) ((JustV $ Undet vTy uc) :: finalRegs)
    @{AreWindedStep' @{IsWindedGValue' @{IsWindedUndet'}} areWinded''} @{CanUnwindAllStep @{CanUnwindGValue} canUnwindAll'} = do
      rec <- unwind' savedRegs gs initRegs finalRegs @{areWinded''} @{canUnwindAll'}
      pure $ (JustV vExpr) :: rec

  unwind' ((JustV vExpr) :: savedRegs) (GValue :: gs) ((JustV vExpr) :: initRegs) ((JustV vExpr) :: finalRegs)
    @{AreWindedStep' @{IsWindedGValue' @{IsWindedDet'}} areWinded''} @{CanUnwindAllStep @{CanUnwindGValue} canUnwindAll'} = do
      rec <- unwind' savedRegs gs initRegs finalRegs @{areWinded''} @{canUnwindAll'}
      pure $ (JustV vExpr) :: rec

  unwind' ((JustV vExpr) :: savedRegs) (GType :: gs) ((JustV $ Undet vTy i) :: initRegs) ((JustV finalExpr) :: finalRegs)
    @{AreWindedStep' @{IsWindedGType'} areWinded''} @{CanUnwindAllStep @{CanUnwindGType} canUnwindAll'} = do
      -- if finalExpr is recursive on initExpr, then try to form an expression with vExpr
      -- else, just Undet vTy
      rec <- unwind' savedRegs gs initRegs finalRegs @{areWinded''} @{canUnwindAll'}
      ?unwind_rhs_8

  unwind' (sr :: savedRegs) (GNothing :: gs) (Unkwn :: initRegs) (fr :: finalRegs)
    @{AreWindedStep' @{IsWindedGNothing'} areWinded''} @{CanUnwindAllStep @{CanUnwindGNothing} canUnwindAll'} = do
      -- if fr is Unkwn, then Unkwn
      -- else
      --   if is determined, then constant
      --   else Undet
      rec <- unwind' savedRegs gs initRegs finalRegs @{areWinded''} @{canUnwindAll'}
      ?unwind'_rhs_9
  -- TODO: I have no idea what to do with these bugs
  unwind' _ _ _ _ = pure never
  where
    never : {n : _} -> VectValue n
    never {n = 0} = []
    never {n = S n'} = Unkwn :: never {n = n'}

  public export
  unwind : {n : _} ->
           (savedRegs : _) -> (gs : _) -> (initRegs, finalRegs : _) ->
           AreWinded {n} savedRegs gs initRegs => CanUnwindAll {n} initRegs gs finalRegs =>
           VectValue n
  unwind savedRegs gs initRegs finalRegs @{TheyAreWinded @{areWinded'}} = evalState 0 $ unwind' savedRegs gs initRegs finalRegs @{areWinded'}

