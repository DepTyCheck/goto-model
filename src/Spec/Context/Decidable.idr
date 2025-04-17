module Spec.Context.Decidable

import public Spec.Context.Loop
import public Decidable.Equality

public export
{g : Guarantee} -> Injective (Guarantee.(::) g) where
  injective Refl = Refl

public export
DecEq Guarantee where
  decEq GValue GValue = Yes Refl
  decEq GType GType = Yes Refl
  decEq GNothing GNothing = Yes Refl
  decEq GValue GType = No $ \case Refl impossible
  decEq GValue GNothing = No $ \case Refl impossible
  decEq GType GValue = No $ \case Refl impossible
  decEq GType GNothing = No $ \case Refl impossible
  decEq GNothing GValue = No $ \case Refl impossible
  decEq GNothing GType = No $ \case Refl impossible

public export
DecEq (VectGuarantee {}) where
  decEq [] [] = Yes Refl
  decEq (g1 :: gs1) (g2 :: gs2) = case decEq g1 g2 of
                                       (Yes Refl) => decEqCong $ decEq gs1 gs2
                                       (No contra) => No $ \case Refl => contra Refl

