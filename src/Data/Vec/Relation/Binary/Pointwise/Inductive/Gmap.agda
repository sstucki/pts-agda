module Data.Vec.Relation.Binary.Pointwise.Inductive.Gmap where

open import Data.Vec using (Vec)
open import Data.Fin
open import Data.Vec.Relation.Binary.Pointwise.Inductive using ([]; _∷_) renaming (Pointwise to All₂) public
import Data.Vec as Vec

module _ {a b c p q} {A : Set a} {B : Set b} {C : Set c} where

  -- A variant of gmap₂ shifting two functions from the binary
  -- relation to the vector.

  gmap₂ : ∀ {d} {D : Set d} {P : A → B → Set p} {Q : C → D → Set q}
            {f₁ : A → C} {f₂ : B → D} →
          (∀ {x y} → P x y → Q (f₁ x) (f₂ y)) → ∀ {k xs ys} →
          All₂ P {k} {k} xs ys → All₂ Q {k} (Vec.map f₁ xs) (Vec.map f₂ ys)
  gmap₂ g [] = []
  gmap₂ g (pxy ∷ pxys) = g pxy ∷ gmap₂ g pxys

  -- A variant of gmap₂ shifting only the first function from the binary
  -- relation to the vector.

  gmap₂₁ : ∀ {P : A → B → Set p} {Q : C → B → Set q} {f : A → C} →
           (∀ {x y} → P x y → Q (f x) y) → ∀ {k xs ys} →
           All₂ P {k} {k} xs ys → All₂ Q {k} (Vec.map f xs) ys
  gmap₂₁ g [] = []
  gmap₂₁ g (pxy ∷ pxys) = g pxy ∷ gmap₂₁ g pxys

  -- A variant of gmap₂ shifting only the second function from the
  -- binary relation to the vector.

  gmap₂₂ : ∀ {P : A → B → Set p} {Q : A → C → Set q} {f : B → C} →
           (∀ {x y} → P x y → Q x (f y)) → ∀ {k xs ys} →
           All₂ P {k} {k} xs ys → All₂ Q {k} xs (Vec.map f ys)
  gmap₂₂ g [] = []
  gmap₂₂ g (pxy ∷ pxys) = g pxy ∷ gmap₂₂ g pxys
