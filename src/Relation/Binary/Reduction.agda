------------------------------------------------------------------------
-- Generic support for reduction relations.
------------------------------------------------------------------------

module Relation.Binary.Reduction where

open import Data.Fin using (Fin)
open import Data.Fin.Substitution
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (Star; ε; _◅_)
import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties as StarProp
open import Data.Nat using (ℕ; _+_)
open import Function using (_∘_)
open import Relation.Binary
open import Relation.Binary.Construct.Closure.Equivalence
open import Relation.Binary.Construct.Closure.Symmetric using (fwd)
import Relation.Binary.PropositionalEquality as PropEq
import Relation.Binary.Reasoning.Setoid as EqReasoning

----------------------------------------------------------------------
-- Generic reduction and equivalence relations

record Reduction (T : ℕ → Set) : Set₁ where

  infix  5  _→1_ _→*_ _↔_

  -- One-step reduction.
  field _→1_ : ∀ {n} → T n → T n → Set

  -- The reflexive transitive closure of _→1_, i.e. finite sequences
  -- of reduction steps.
  _→*_ : ∀ {n} → T n → T n → Set
  _→*_ = Star _→1_

  -- The reflexive, transitive and symmetric closure (aka the
  -- equivalence closure) of _→1_.
  _↔_ : ∀ {n} → T n → T n → Set
  _↔_ = EqClosure _→1_


-- All remaining submodules are parametrized by a given reduction.
module _ {T} (reduction : Reduction T) where
  open Reduction reduction

  ----------------------------------------------------------------------
  -- Properties of the reductions/equivalence

  -- Inclusions.

  →1⇒→* : ∀ {n} {a b : T n} → a →1 b → a →* b
  →1⇒→* a→b = a→b ◅ ε

  →*⇒↔ : ∀ {n} {a b : T n} → a →* b → a ↔ b
  →*⇒↔ a→*b = Star.map fwd a→*b

  →1⇒↔ : ∀ {n} {a b : T n} → a →1 b → a ↔ b
  →1⇒↔ = →*⇒↔ ∘ →1⇒→*

  -- Reductions are preorders.
  →*-predorder : ∀ {n : ℕ} → Preorder _ _ _
  →*-predorder {n} = StarProp.preorder (_→1_ {n})

  -- Preorder reasoning for reductions.
  module →*-Reasoning {n} = StarProp.StarReasoning (_→1_ {n})

  -- Terms together with equivalence form a setoid.
  ↔-setoid : ∀ {n : ℕ} → Setoid _ _
  ↔-setoid {n} = setoid (_→1_ {n})

  -- Equational reasoning for ↔-equivalence.
  module ↔-Reasoning {n : ℕ} where
    open EqReasoning (↔-setoid {n}) public
    open Setoid (↔-setoid {n}) using (sym)

    infixr 2 _→⟨_⟩_ _←⟨_⟩_ _→*⟨_⟩_ _←*⟨_⟩_

    _→⟨_⟩_ : ∀ a {b c} → a →1 b → b IsRelatedTo c → a IsRelatedTo c
    a →⟨ a→b ⟩ b≡c = a ≈⟨ →1⇒↔ a→b ⟩ b≡c

    _←⟨_⟩_ : ∀ a {b c} → b →1 a → b IsRelatedTo c → a IsRelatedTo c
    a ←⟨ a←b ⟩ b≡c = a ≈⟨ sym (→1⇒↔ a←b) ⟩ b≡c

    _→*⟨_⟩_ : ∀ a {b c} → a →* b → b IsRelatedTo c → a IsRelatedTo c
    a →*⟨ a→*b ⟩ b≡c = a ≈⟨ →*⇒↔ a→*b ⟩ b≡c

    _←*⟨_⟩_ : ∀ a {b c} → b →* a → b IsRelatedTo c → a IsRelatedTo c
    a ←*⟨ a←*b ⟩ b≡c = a ≈⟨ sym (→*⇒↔ a←*b) ⟩ b≡c


  ----------------------------------------------------------------------
  -- Substitutions in reductions/equivalence
  --
  -- The applications _/→1_, _/→*_ and _/↔_ below may be considered
  -- substitution lemmas, i.e. they establish the commutativity of the
  -- respective reductions/equivalence with substitutions.

  record RedSubstApp {T′} (app : Application T T′) : Set where
    open Application app
    open PropEq

    infixl 8 _/→1_ _/→*_ _/↔_

    field
      -- Substitution commutes with one-step reduction.
      _/→1_ : ∀ {m n a b} → a →1 b → (σ : Sub T′ m n) → a / σ →1 b / σ

    -- Substitution commutes with β-reduction.
    _/→*_ : ∀ {m n a b} → a →* b → (σ : Sub T′ m n) → a / σ →* b / σ
    a→*b /→* σ = Star.gmap (λ a → a / σ) (λ a→b → a→b /→1 σ) a→*b

    -- Substitution commutes with β-equivalence.
    _/↔_ : ∀ {m n a b} → a ↔ b → (σ : Sub T′ m n) → a / σ ↔ b / σ
    a≡b /↔ σ = gmap (λ a → a / σ) (λ a→b → a→b /→1 σ) a≡b
