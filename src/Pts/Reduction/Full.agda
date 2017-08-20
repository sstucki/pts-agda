------------------------------------------------------------------------
-- Full β-reduction in pure type systems (PTS)
------------------------------------------------------------------------

module Pts.Reduction.Full where

open import Data.Fin.Substitution
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Star using (ε; _◅_; map; gmap; _⋆)
open import Data.Sum using ([_,_])
open import Data.Product using (_,_; ∃; _×_)
open import Function using (_∘_)
open import Relation.Binary
import Relation.Binary.EquivalenceClosure as EqClos
import Relation.Binary.PropositionalEquality as P
import Relation.Binary.SymmetricClosure as SymClos
open import Relation.Binary.Reduction
import Function.Equivalence as Equiv

open import Pts.Syntax
open import Pts.Reduction.Parallel as Par hiding (reduction; _⋄*_; Π-inj)


-- All remaining submodules are parametrized by a given set of sorts.
module _ {Sort : Set} where

  open Syntax       Sort
  open Substitution Sort using (_[_])

  ----------------------------------------------------------------------
  -- Full β-reduction and equivalence relations

  infixl 9  _·₁_ _·₂_
  infix  5  _→β_

  -- One-step β-reduction.
  data _→β_ {n} : Term n → Term n → Set where
    cont : ∀ a b c                    → (ƛ a b) · c →β b [ c ]
    Π₁   : ∀ {a₁ a₂} → a₁ →β a₂ → ∀ b →      Π a₁ b →β Π a₂ b
    Π₂   : ∀ {b₁ b₂} a → b₁ →β b₂     →      Π a b₁ →β Π a b₂
    ƛ₁   : ∀ {a₁ a₂} → a₁ →β a₂ → ∀ b →      ƛ a₁ b →β ƛ a₂ b
    ƛ₂   : ∀ {b₁ b₂} a → b₁ →β b₂     →      ƛ a b₁ →β ƛ a b₂
    _·₁_ : ∀ {a₁ a₂} → a₁ →β a₂ → ∀ b →      a₁ · b →β a₂ · b
    _·₂_ : ∀ {b₁ b₂} a → b₁ →β b₂     →      a · b₁ →β a · b₂

  reduction : Reduction Term
  reduction = record { _→1_ = _→β_ }

  -- Full beta reduction and equivalence.
  open Reduction reduction public renaming (_→*_ to _→β*_; _↔_ to _≡β_)


  ----------------------------------------------------------------------
  -- Substitutions in full β-reductions/equivalence
  --
  -- The applications _/→β_, _/→β*_ and _/≡β_ below may be considered
  -- substitution lemmas, i.e. they establish the commutativity of the
  -- respective reductions/equivalence with substitutions.

  -- Application of generic substitutions to the
  -- reductions/equivalence.
  record BetaSubstApp {T} (l : Lift T Term) : Set where
    open Lift l
    open SubstApp Sort l
    open P hiding ([_])

    -- Substitutions commute.
    field /-sub-↑ : ∀ {m n} a b (σ : Sub T m n) →
                    a [ b ] / σ ≡ (a / σ ↑) [ b / σ ]

    infixl 8 _/→β_

    -- Substitution commutes with one-step β-reduction.
    _/→β_ : ∀ {m n a b} → a →β b → (σ : Sub T m n) → a / σ →β b / σ
    cont a b c /→β σ =
      subst (_→β_ _) (sym (/-sub-↑ b c σ)) (cont (a / σ) (b / σ ↑) (c / σ))
    Π₁ a₁→a₂ b /→β σ = Π₁ (a₁→a₂ /→β σ) (b / σ ↑)
    Π₂ a b₁→b₂ /→β σ = Π₂ (a / σ) (b₁→b₂ /→β σ ↑)
    ƛ₁ a₁→a₂ b /→β σ = ƛ₁ (a₁→a₂ /→β σ) (b / σ ↑)
    ƛ₂ a b₁→b₂ /→β σ = ƛ₂ (a / σ) (b₁→b₂ /→β σ ↑)
    a₁→a₂ ·₁ b /→β σ = (a₁→a₂ /→β σ) ·₁ (b / σ)
    a ·₂ b₁→b₂ /→β σ = (a / σ) ·₂ (b₁→b₂ /→β σ)

    redSubstApp : RedSubstApp reduction (record { _/_ = _/_ })
    redSubstApp = record { _/→1_ = _/→β_ }

    open RedSubstApp redSubstApp public
      hiding (_/→1_) renaming (_/→*_ to _/→β*_; _/↔_ to _/≡β_)

  -- Term substitutions in reductions/equivalences.
  module BetaSubstitution where
    open Substitution Sort
      using (termSubst; weaken; sub-commutes; varLiftSubLemmas)

    -- Application of renamings to reductions/equivalences.
    varSubstApp : BetaSubstApp (TermSubst.varLift termSubst)
    varSubstApp = record { /-sub-↑ = /-sub-↑ }
      where open LiftSubLemmas varLiftSubLemmas
    private module V = BetaSubstApp varSubstApp

    -- Weakening of one-step β-reductions.
    weaken-→β : ∀ {n} {a b : Term n} → a →β b → weaken a →β weaken b
    weaken-→β a→b = a→b V./→β VarSubst.wk

    -- Weakening of β-reductions.
    weaken-→β* : ∀ {n} {a b : Term n} → a →β* b → weaken a →β* weaken b
    weaken-→β* = gmap weaken weaken-→β

    -- Weakening of β-equivalences.
    weaken-≡β : ∀ {n} {a b : Term n} → a ≡β b → weaken a ≡β weaken b
    weaken-≡β = EqClos.gmap weaken weaken-→β

    -- Application of term substitutions to reductions/equivalences.
    termSubstApp : BetaSubstApp (TermSubst.termLift termSubst)
    termSubstApp = record { /-sub-↑ = λ a _ _ → sub-commutes a }
    open BetaSubstApp termSubstApp public


  ----------------------------------------------------------------------
  -- Simple properties of the β-reductions/equivalence

  -- Inclusions.
  →β⇒→β* = →1⇒→* reduction
  →β*⇒≡β = →*⇒↔  reduction
  →β⇒≡β  = →1⇒↔  reduction

  -- β-reduction is a preorder.
  →β*-predorder = →*-predorder reduction

  -- Preorder reasoning for β-reduction.
  module →β*-Reasoning = →*-Reasoning reduction

  -- Terms together with β-equivalence form a setoid.
  ≡β-setoid = ↔-setoid reduction

  -- Equational reasoning for β-equivalence.
  module ≡β-Reasoning = ↔-Reasoning reduction


  ----------------------------------------------------------------------
  -- Relationships between β-reduction and parallel reduction

  -- One-step β-reduction implies one-step parallel reduction.
  →β⇒⇛ : ∀ {n} {a b : Term n} → a →β b → a ⇛ b
  →β⇒⇛ (cont a b c) = cont refl refl
  →β⇒⇛ (Π₁ a₁→a₂ b) = Π (→β⇒⇛ a₁→a₂) refl
  →β⇒⇛ (Π₂ a b₁→b₂) = Π refl (→β⇒⇛ b₁→b₂)
  →β⇒⇛ (ƛ₁ a₁→a₂ b) = ƛ (→β⇒⇛ a₁→a₂) refl
  →β⇒⇛ (ƛ₂ a b₁→b₂) = ƛ refl (→β⇒⇛ b₁→b₂)
  →β⇒⇛ (a₁→a₂ ·₁ b) = →β⇒⇛ a₁→a₂ · refl
  →β⇒⇛ (a ·₂ b₁→b₂) = refl · →β⇒⇛ b₁→b₂

  -- β-reduction implies parallel reduction.
  →β*⇒⇛* : ∀ {n} {a b : Term n} → a →β* b → a ⇛* b
  →β*⇒⇛* = map →β⇒⇛

  -- β-equivalence implies parallel equivalence.
  ≡β⇒≡p : ∀ {n} {a b : Term n} → a ≡β b → a ≡p b
  ≡β⇒≡p = EqClos.map →β⇒⇛

  open →*-Reasoning reduction

  -- One-step parallel reduction implies β-reduction.
  ⇛⇒→β* : ∀ {n} {a b : Term n} → a ⇛ b → a →β* b
  ⇛⇒→β* refl            = ε
  ⇛⇒→β* (Π {a₁} {a₂} {b₁} {b₂} a₁⇛a₂ b₁⇛b₂) = begin
    Π a₁ b₁   ⟶⋆⟨ gmap (λ a → Π a _) (λ a₁→a₂ → Π₁ a₁→a₂ _) (⇛⇒→β* a₁⇛a₂) ⟩
    Π a₂ b₁   ⟶⋆⟨ gmap (Π _) (Π₂ _) (⇛⇒→β* b₁⇛b₂) ⟩
    Π a₂ b₂   ∎
  ⇛⇒→β* (ƛ {a₁} {a₂} {b₁} {b₂} a₁⇛a₂ b₁⇛b₂) = begin
    ƛ a₁ b₁   ⟶⋆⟨ gmap (λ a → ƛ a _) (λ a₁→a₂ → ƛ₁ a₁→a₂ _) (⇛⇒→β* a₁⇛a₂) ⟩
    ƛ a₂ b₁   ⟶⋆⟨ gmap (ƛ _) (ƛ₂ _) (⇛⇒→β* b₁⇛b₂) ⟩
    ƛ a₂ b₂   ∎
  ⇛⇒→β* (_·_ {a₁} {a₂} {b₁} {b₂} a₁⇛a₂ b₁⇛b₂) = begin
    a₁ · b₁   ⟶⋆⟨ gmap (λ a → a · _) (λ a₁→a₂ → a₁→a₂ ·₁ _) (⇛⇒→β* a₁⇛a₂) ⟩
    a₂ · b₁   ⟶⋆⟨ gmap (_·_ _) (_·₂_ _) (⇛⇒→β* b₁⇛b₂) ⟩
    a₂ · b₂   ∎
  ⇛⇒→β* (cont {a} {b₁} {b₂} {c₁} {c₂} b₁⇛b₂ c₁⇛c₂) = begin
    (ƛ a b₁) · c₁   ⟶⋆⟨ gmap (λ b → (ƛ _ b) · _)
                             (λ b₁→b₂ → (ƛ₂ _ b₁→b₂) ·₁ _) (⇛⇒→β* b₁⇛b₂) ⟩
    (ƛ a b₂) · c₁   ⟶⋆⟨ gmap (_·_ _) (_·₂_ _) (⇛⇒→β* c₁⇛c₂) ⟩
    (ƛ a b₂) · c₂   ⟶⟨ cont a b₂ c₂ ⟩
    b₂ [ c₂ ]       ∎

  -- Parallel reduction implies β-reduction.
  ⇛*⇒→β* : ∀ {n} {a b : Term n} → a ⇛* b → a →β* b
  ⇛*⇒→β* a⇛*b = (⇛⇒→β* ⋆) a⇛*b

  -- Parallel equivalence implies β-equivalence.
  ≡p⇒≡β : ∀ {n} {a b : Term n} → a ≡p b → a ≡β b
  ≡p⇒≡β a≡b = ([ ⇛⇒≡β , sym ∘ ⇛⇒≡β ] ⋆) a≡b
    where
      open Setoid ≡β-setoid using (sym)

      ⇛⇒≡β : ∀ {n} {a b : Term n} → a ⇛ b → a ≡β b
      ⇛⇒≡β = →*⇒↔ reduction ∘ ⇛⇒→β*

  open Equiv using (_⇔_; equivalence)

  -- Full β-reduction is equivalent to parallel reduction.
  →β*-⇛*-equivalence : ∀ {n} {a b : Term n} → a →β* b ⇔ a ⇛* b
  →β*-⇛*-equivalence = equivalence →β*⇒⇛* ⇛*⇒→β*

  -- β-equivalence is equivalent to parallel equivalence.
  ≡β-≡p-equivalence : ∀ {n} {a b : Term n} → a ≡β b ⇔ a ≡p b
  ≡β-≡p-equivalence = equivalence ≡β⇒≡p ≡p⇒≡β

  -- Shorthand for single-variable substitutions lifted to β-redcution.
  _[→β_] : ∀ {n} a {b₁ b₂ : Term n} → b₁ →β b₂ → a [ b₁ ] →β* a [ b₂ ]
  a [→β b₁→b₂ ] = ⇛⇒→β* (a / sub (→β⇒⇛ b₁→b₂))
    where open ParSubstitution using (_/_; sub)

  open P using (_≡_)

  -- Shapes are preserved by full β-reduction.

  sort-→β* : ∀ {n s} {a : Term n} → sort s →β* a → sort s ≡ a
  sort-→β* ε = P.refl
  sort-→β* (() ◅ _)

  ƛ-→β* : ∀ {n} {a : Term n} {b c} → ƛ a b →β* c →
          ∃ λ a′ → ∃ λ b′ → a →β* a′ × b →β* b′ × ƛ a′ b′ ≡ c
  ƛ-→β* λab→*c =
    let a′ , b′ , a⇛a′ , b⇛b′ , λa′b′≡c = ƛ-⇛* (→β*⇒⇛* λab→*c)
    in a′ , b′ , ⇛*⇒→β* a⇛a′ , ⇛*⇒→β* b⇛b′ , λa′b′≡c

  Π-→β* : ∀ {n} {a : Term n} {b c} → Π a b →β* c →
          ∃ λ a′ → ∃ λ b′ → a →β* a′ × b →β* b′ × Π a′ b′ ≡ c
  Π-→β* Πab→*c =
    let a′ , b′ , a⇛a′ , b⇛b′ , Πa′b′≡c = Π-⇛* (→β*⇒⇛* Πab→*c)
    in a′ , b′ , ⇛*⇒→β* a⇛a′ , ⇛*⇒→β* b⇛b′ , Πa′b′≡c


  ----------------------------------------------------------------------
  -- Confluence (aka the Church-Rosser property) of full β-reduction
  --
  -- Full β-reduction is confluent, i.e.  i.e. for any pair a →β* b₁,
  -- a →β* b₂ of parallel reductions, there is a term c, such that
  --
  --                               →β*
  --                           a ------→ b₂
  --                           |         :
  --                       →β* |         : →β*
  --                           ↓   →β*   ↓
  --                           b₁ ·····→ c
  --
  -- commutes.

  -- Confluence of _→β*_ (aka the Church-Rosser property).
  _⋄*_ : ∀ {n} {a b₁ b₂ : Term n} →
         a →β* b₁ → a →β* b₂ → ∃ λ c → b₁ →β* c × b₂ →β* c
  a→*b₁ ⋄* a→*b₂ =
    let c , b₁⇛*c , b₂⇛*c = (→β*⇒⇛* a→*b₁) Par.⋄* (→β*⇒⇛* a→*b₂)
    in c , ⇛*⇒→β* b₁⇛*c , ⇛*⇒→β* b₂⇛*c

  -- Factorization of β-equivalence into β-reductions.
  ≡β⇒→β* : ∀ {n} {a b : Term n} → a ≡β b → ∃ λ c → a →β* c × b →β* c
  ≡β⇒→β* a≡b =
    let c , a⇛*c , b⇛*c = ≡p⇒⇛* (≡β⇒≡p a≡b)
    in c , ⇛*⇒→β* a⇛*c , ⇛*⇒→β* b⇛*c

  -- Π-injectivity (with respect to ≡β).
  Π-inj : ∀ {n} {a₁ a₂ : Term n} {b₁ b₂} → Π a₁ b₁ ≡β Π a₂ b₂ →
          a₁ ≡β a₂ × b₁ ≡β b₂
  Π-inj Πa₁b₁≡Πa₂b₂ =
    let a₁≡a₂ , b₁≡b₂ = Par.Π-inj (≡β⇒≡p Πa₁b₁≡Πa₂b₂)
    in ≡p⇒≡β a₁≡a₂ , ≡p⇒≡β b₁≡b₂

  -- β-equivalence on sorts implies syntactic equivalence.
  sort-≡β : ∀ {n s₁ s₂} → sort {n} s₁ ≡β sort s₂ → s₁ ≡ s₂
  sort-≡β s₁≡βs₂ = Par.sort-≡p (≡β⇒≡p s₁≡βs₂)
