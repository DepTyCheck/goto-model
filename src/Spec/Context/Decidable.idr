module Spec.Context.Decidable

import public Spec.Value.Decidable
import public Spec.Context


public export
{k : _} -> Injective (Src k) where
  injective Refl = Refl

public export
{n : _} -> {s : Source n} -> Injective (Source.(::) s) where
  injective Refl = Refl

public export
{g : _} -> Injective (Guarantee.(::) g) where
  injective Refl = Refl

public export
{k : _} -> Injective (SCtx k) where
  injective Refl = Refl

public export
{n : _} -> {l : Loop n} -> Injective (Loop.(::) l) where
  injective Refl = Refl


public export
DecEq (Source n) where
  decEq (Src k vs) (Src k' vs') = case decEq k k' of
                                       (Yes Refl) => decEqCong $ decEq vs vs'
                                       (No contra) => No $ \case Refl => contra Refl

public export
DecEq (ListSource n) where
  decEq [] [] = Yes Refl
  decEq [] (_ :: _) = No $ \case Refl impossible
  decEq (_ :: _) [] = No $ \case Refl impossible
  decEq (s :: ss) (s' :: ss') = case decEq s s' of
                                     (Yes Refl) => decEqCong $ decEq ss ss'
                                     (No contra) => No $ \case Refl => contra Refl

public export
DecEq Guarantee where
  decEq SavesValue SavesValue = Yes Refl
  decEq SavesType SavesType = Yes Refl
  decEq SavesNothing SavesNothing = Yes Refl
  decEq SavesValue SavesType = No $ \case Refl impossible
  decEq SavesValue SavesNothing = No $ \case Refl impossible
  decEq SavesType SavesValue = No $ \case Refl impossible
  decEq SavesType SavesNothing = No $ \case Refl impossible
  decEq SavesNothing SavesValue = No $ \case Refl impossible
  decEq SavesNothing SavesType = No $ \case Refl impossible

public export
DecEq (Guarantees n) where
  decEq [] [] = Yes Refl
  decEq (g :: gs) (g' :: gs') = case decEq g g' of
                                     (Yes Refl) => decEqCong $ decEq gs gs'
                                     (No contra) => No $ \case Refl => contra Refl

public export
DecEq (SavedContext n) where
  decEq (SCtx k vs) (SCtx k' vs') = case decEq k k' of
                                         (Yes Refl) => decEqCong $ decEq vs vs'
                                         (No contra) => No $ \case Refl => contra Refl

public export
DecEq (Loop n) where
  decEq (L savedC initC gs ls)
        (L savedC' initC' gs' ls')
    with (decEq savedC savedC', decEq initC initC', decEq gs gs', decEq ls ls')
      decEq (L savedC initC gs ls)
            (L savedC initC gs ls) | (Yes Refl, Yes Refl, Yes Refl, Yes Refl) = Yes Refl
      decEq (L savedC initC gs ls)
            (L savedC initC gs ls') | (Yes Refl, Yes Refl, Yes Refl, No contra) = No $ \case Refl => contra Refl
      decEq (L savedC initC gs ls)
            (L savedC initC gs' ls') | (Yes Refl, Yes Refl, No contra, _) = No $ \case Refl => contra Refl
      decEq (L savedC initC gs ls)
            (L savedC initC' gs' ls') | (Yes Refl, No contra, _, _) = No $ \case Refl => contra Refl
      decEq (L savedC initC gs ls)
            (L savedC' initC' gs' ls') | (No contra, _, _, _) = No $ \case Refl => contra Refl

public export
DecEq (ListLoop n) where
  decEq [] [] = Yes Refl
  decEq [] (_ :: _) = No $ \case Refl impossible
  decEq (_ :: _) [] = No $ \case Refl impossible
  decEq (l :: ll) (l' :: ll') = case decEq l l' of
                                     (Yes Refl) => decEqCong $ decEq ll ll'
                                     (No contra) => No $ \case Refl => contra Refl

public export
DecEq (Context n) where
  decEq (Ctx ols uc regs isInLB fs)
        (Ctx ols' uc' regs' isInLB' fs')
    with (decEq ols ols', decEq uc uc', decEq regs regs', decEq isInLB isInLB', decEq fs fs')
      decEq (Ctx ols uc regs isInLB fs)
            (Ctx ols uc regs isInLB fs)
        | (Yes Refl, Yes Refl, Yes Refl, Yes Refl, Yes Refl) = Yes Refl
      decEq (Ctx ols uc regs isInLB fs)
            (Ctx ols uc regs isInLB fs')
        | (Yes Refl, Yes Refl, Yes Refl, Yes Refl, No contra) = No $ \case Refl => contra Refl
      decEq (Ctx ols uc regs isInLB fs)
            (Ctx ols uc regs isInLB' fs')
        | (Yes Refl, Yes Refl, Yes Refl, No contra, _) = No $ \case Refl => contra Refl
      decEq (Ctx ols uc regs isInLB fs)
            (Ctx ols uc regs' isInLB' fs')
        | (Yes Refl, Yes Refl, No contra, _, _) = No $ \case Refl => contra Refl
      decEq (Ctx ols uc regs isInLB fs)
            (Ctx ols uc' regs' isInLB' fs')
        | (Yes Refl, No contra, _, _, _) = No $ \case Refl => contra Refl
      decEq (Ctx ols uc regs isInLB fs)
            (Ctx ols' uc' regs' isInLB' fs')
        | (No contra, _, _, _, _) = No $ \case Refl => contra Refl

