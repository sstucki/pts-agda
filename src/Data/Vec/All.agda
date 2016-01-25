------------------------------------------------------------------------
-- Vectors where all elements satisfy a given property
--
-- Adapted from Data.List.All module of the Agda standard library
------------------------------------------------------------------------

module Data.Vec.All where

open import Data.Vec as Vec using (Vec; []; _∷_; zip)
open import Data.Vec.Properties using (map-id)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (suc)
open import Function
open import Level using (_⊔_)
open import Data.Product as Product using (curry; uncurry; proj₁; proj₂)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Unary using (Decidable) renaming (_⊆_ to _⋐_)
open import Relation.Binary.PropositionalEquality

-- All P xs means that all elements in xs satisfy P.

infixr 5 _∷_

data All {a p} {A : Set a}
         (P : A → Set p) : ∀ {k} → Vec A k → Set (p ⊔ a) where
  []  : All P []
  _∷_ : ∀ {k x} {xs : Vec A k} (px : P x) (pxs : All P xs) → All P (x ∷ xs)

head : ∀ {a p} {A : Set a} {P : A → Set p} {k x} {xs : Vec A k} →
       All P (x ∷ xs) → P x
head (px ∷ pxs) = px

tail : ∀ {a p} {A : Set a} {P : A → Set p} {k x} {xs : Vec A k} →
       All P (x ∷ xs) → All P xs
tail (px ∷ pxs) = pxs

lookup : ∀ {a p} {A : Set a} {P : A → Set p} {k} {xs : Vec A k} →
         (i : Fin k) → All P xs → P (Vec.lookup i xs)
lookup ()      []
lookup zero    (px ∷ pxs) = px
lookup (suc i) (px ∷ pxs) = lookup i pxs

tabulate : ∀ {a p} {A : Set a} {P : A → Set p} {k} {xs : Vec A k} →
           (∀ x → P x) → All P xs
tabulate {xs = []}     hyp = []
tabulate {xs = x ∷ xs} hyp = hyp x ∷ tabulate hyp

map : ∀ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q} {k} →
      P ⋐ Q → All P {k} ⋐ All Q {k}
map g []         = []
map g (px ∷ pxs) = g px ∷ map g pxs

all : ∀ {a p} {A : Set a} {P : A → Set p} {k} →
      Decidable P → Decidable (All P {k})
all p []       = yes []
all p (x ∷ xs) with p x
all p (x ∷ xs) | yes px = Dec.map′ (_∷_ px) tail (all p xs)
all p (x ∷ xs) | no ¬px = no (¬px ∘ head)

zipWith : ∀ {a b c p q r} {A : Set a} {B : Set b} {C : Set c} {_⊕_ : A → B → C}
          {P : A → Set p} {Q : B → Set q} {R : C → Set r} →
          (∀ {x y} → P x → Q y → R (x ⊕ y)) →
          ∀ {k xs ys} → All P {k} xs → All Q {k} ys →
          All R {k} (Vec.zipWith _⊕_ xs ys)
zipWith _⊕_ {xs = []}     {[]}     []         []         = []
zipWith _⊕_ {xs = x ∷ xs} {y ∷ ys} (px ∷ pxs) (qy ∷ qys) =
  px ⊕ qy ∷ zipWith _⊕_ pxs qys


-- A shorthand for a pair of vectors point-wise satisfying a binary
-- predicate.
All₂ : ∀ {a p} {A B : Set a} (P : A → B → Set p) {k} →
       Vec A k → Vec B k → Set _
All₂ P xs ys = All (uncurry P) (zip xs ys)

-- A variant of lookup tailored to All₂.
lookup₂ : ∀ {a p} {A B : Set a} {P : A → B → Set p} {k}
            {xs : Vec A k} {ys : Vec B k} →
          (i : Fin k) → All₂ P xs ys → P (Vec.lookup i xs) (Vec.lookup i ys)
lookup₂ {P = P} {xs = xs} {ys} i pxys =
  subst₂ P (proj₁-lookup-zip i xs ys) (proj₂-lookup-zip i xs ys)
           (lookup i pxys)
  where
    open Vec using (Vec; zip)

    proj₁-lookup-zip : ∀ {a n} {A B : Set a}
                       (i : Fin n) (xs : Vec A n) (ys : Vec B n) →
                       proj₁ (Vec.lookup i (zip xs ys)) ≡ Vec.lookup i xs
    proj₁-lookup-zip ()      []       []
    proj₁-lookup-zip zero    (x ∷ xs) (y ∷ ys) = refl
    proj₁-lookup-zip (suc i) (x ∷ xs) (y ∷ ys) = proj₁-lookup-zip i xs ys

    proj₂-lookup-zip : ∀ {a n} {A B : Set a}
                       (i : Fin n) (xs : Vec A n) (ys : Vec B n) →
                       proj₂ (Vec.lookup i (zip xs ys)) ≡ Vec.lookup i ys
    proj₂-lookup-zip ()      []       []
    proj₂-lookup-zip zero    (x ∷ xs) (y ∷ ys) = refl
    proj₂-lookup-zip (suc i) (x ∷ xs) (y ∷ ys) = proj₂-lookup-zip i xs ys

-- A variant of map tailored to All₂.
map₂ : ∀ {a p q} {A B : Set a} {P : A → B → Set p} {Q : A → B → Set q} →
       (∀ {x y} → P x y → Q x y) →
       ∀ {k xs ys} → All₂ P {k} xs ys → All₂ Q {k} xs ys
map₂ g = map g

------------------------------------------------------------------------
-- Properties

-- Functions can be shifted between the predicate and the vector.

All-map : ∀ {a b p} {A : Set a} {B : Set b} {P : B → Set p}
            {f : A → B} {k} {xs : Vec A k} →
          All (P ∘ f) xs → All P (Vec.map f xs)
All-map []         = []
All-map (px ∷ pxs) = px ∷ All-map pxs

map-All : ∀ {a b p} {A : Set a} {B : Set b} {P : B → Set p}
            {f : A → B} {k} {xs : Vec A k} →
          All P (Vec.map f xs) → All (P ∘ f) xs
map-All {xs = []}    []       = []
map-All {xs = _ ∷ _} (px ∷ pxs) = px ∷ map-All pxs

-- A variant of map.
gmap : ∀ {a b p q}
         {A : Set a} {B : Set b} {P : A → Set p} {Q : B → Set q}
         {f : A → B} {k} →
       P ⋐ Q ∘ f → All P {k} ⋐ All Q {k} ∘ Vec.map f
gmap g = All-map ∘ map g

-- A variant of All-map tailored to All₂.
All₂-map : ∀ {a b p} {A₁ A₂ : Set a} {B₁ B₂ : Set b} {P : B₁ → B₂ → Set p}
           {f₁ : A₁ → B₁} {f₂ : A₂ → B₂} {k} {xs : Vec A₁ k} {ys : Vec A₂ k} →
           All₂ (λ x y → P (f₁ x) (f₂ y)) xs ys →
           All₂ P (Vec.map f₁ xs) (Vec.map f₂ ys)
All₂-map {xs = []}    {ys = []}    []         = []
All₂-map {xs = _ ∷ _} {ys = _ ∷ _} (px ∷ pxs) = px ∷ All₂-map pxs

-- A variant of gmap tailored to All₂.
gmap₂ : ∀ {a b p q} {A₁ A₂ : Set a} {B₁ B₂ : Set b}
          {P : A₁ → A₂ → Set p} {Q : B₁ → B₂ → Set q}
          {f₁ : A₁ → B₁} {f₂ : A₂ → B₂} →
        (∀ {x y} → P x y → Q (f₁ x) (f₂ y)) → ∀ {k xs ys} →
        All₂ P {k} xs ys → All₂ Q {k} (Vec.map f₁ xs) (Vec.map f₂ ys)
gmap₂ g = All₂-map ∘ map g

-- A variant of gmap₂ shifting only the first function in a binary
-- predicate to the vector.
gmap₂₁ : ∀ {a p q} {A₁ A₂ : Set a} {B : Set a}
           {P : A₁ → A₂ → Set p} {Q : B → A₂ → Set q} {f : A₁ → B} →
         (∀ {x y} → P x y → Q (f x) y) → ∀ {k xs ys} →
         All₂ P {k} xs ys → All₂ Q {k} (Vec.map f xs) ys
gmap₂₁ g = subst (All₂ _ _) (map-id _) ∘ All₂-map {f₂ = id} ∘ map g

-- A variant of gmap₂ shifting only the second function in a binary
-- predicate to the vector.
gmap₂₂ : ∀ {a p q} {A₁ A₂ : Set a} {B : Set a}
           {P : A₁ → A₂ → Set p} {Q : A₁ → B → Set q} {f : A₂ → B} →
         (∀ {x y} → P x y → Q x (f y)) → ∀ {k xs ys} →
         All₂ P {k} xs ys → All₂ Q {k} xs (Vec.map f ys)
gmap₂₂ g = subst (flip (All₂ _) _) (map-id _) ∘ All₂-map {f₁ = id} ∘ map g

-- Composition of binary predicates lifted to All₂.
comp : ∀ {a p} {A : Set a} {B : Set a} {C : Set a}
       {P : A → B → Set p} {Q : B → C → Set p} {R : A → C → Set p} →
       (∀ {x y z} → P x y → Q y z → R x z) →
       ∀ {k xs ys zs} → All₂ P {k} xs ys → All₂ Q {k} ys zs → All₂ R {k} xs zs
comp _⊙_ {xs = []}     {[]}     {[]}     []           []           = []
comp _⊙_ {xs = x ∷ xs} {y ∷ ys} {z ∷ zs} (pxy ∷ pxys) (qzx ∷ qzxs) =
  pxy ⊙ qzx ∷ comp _⊙_ pxys qzxs
