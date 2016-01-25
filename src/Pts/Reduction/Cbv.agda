------------------------------------------------------------------------
-- Call-by-value (CBV) reduction in pure type systems (PTS)
------------------------------------------------------------------------

module Pts.Reduction.Cbv where

open import Data.Fin.Substitution
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Star using (map; gmap)
import Relation.Binary.EquivalenceClosure as EqClos
import Relation.Binary.PropositionalEquality as PropEq

open import Pts.Syntax
open import Pts.Reduction
open import Pts.Reduction.Full as Full hiding (reduction)


-- All remaining submodules are parametrized by a given set of sorts.
module _ {Sort : Set} where

  open Syntax       Sort
  open Substitution Sort using (_[_])

  ----------------------------------------------------------------------
  -- Call-by-value (CBV) reduction and equivalence relations

  -- Untyped values with up to n free variables.
  data Val {n} : Term n → Set where
    sort : ∀ s   → Val (sort s)  -- sort
    Π    : ∀ a b → Val (Π a b)   -- dependent product
    ƛ    : ∀ a b → Val (ƛ a b)   -- abstraction

  infixl 9  _·₁_ _·₂_
  infix  5  _→v_

  -- One-step CBV reduction.
  data _→v_ {n} : Term n → Term n → Set where
    cont : ∀ a b {c} (v : Val c)              → (ƛ a b) · c →v b [ c ]
    _·₁_ : ∀ {a₁ a₂} → a₁ →v a₂ → ∀ b         →      a₁ · b →v a₂ · b
    _·₂_ : ∀ {a b₁ b₂} (v : Val a) → b₁ →v b₂ →      a · b₁ →v a · b₂

  reduction : Reduction Term
  reduction = record { _→1_ = _→v_ }

  -- CBV reduction and equivalence.
  open Reduction reduction public renaming (_→*_ to _→v*_; _↔_ to _≡v_)


  ----------------------------------------------------------------------
  -- Substitutions in CBV reductions/equivalence
  --
  -- The applications _/→v_, _/→v*_ and _/≡v_ below may be considered
  -- substitution lemmas, i.e. they establish the commutativity of the
  -- respective reductions/equivalence with substitutions.

  -- Application of generic substitutions to the
  -- reductions/equivalence.
  record CbvSubstApp {T} (l : Lift T Term) : Set where
    open Lift l
    open SubstApp Sort l
    open PropEq hiding ([_])

    -- Substitutions commute.
    field /-sub-↑ : ∀ {m n} a b (σ : Sub T m n) →
                    a [ b ] / σ ≡ (a / σ ↑) [ b / σ ]

    infixl 8 _/Val_ _/→v_

    -- Application of substitutions preserves values.
    _/Val_ : ∀ {m n a} → Val a → (σ : Sub T m n) → Val (a / σ)
    sort s /Val σ = sort s
    Π a b  /Val σ = Π (a / σ) (b / σ ↑)
    ƛ a b  /Val σ = ƛ (a / σ) (b / σ ↑)

    -- Substitution commutes with one-step reduction.
    _/→v_ : ∀ {m n a b} → a →v b → (σ : Sub T m n) → a / σ →v b / σ
    cont a b c /→v σ =
      subst (_→v_ _) (sym (/-sub-↑ b _ σ)) (cont (a / σ) (b / σ ↑) (c /Val σ))
    a₁→a₂ ·₁ b /→v σ = (a₁→a₂ /→v σ) ·₁ (b / σ)
    a ·₂ b₁→b₂ /→v σ = (a /Val σ) ·₂ (b₁→b₂ /→v σ)

    redSubstApp : RedSubstApp reduction (record { _/_ = _/_ })
    redSubstApp = record { _/→1_ = _/→v_ }

    open RedSubstApp reduction redSubstApp public
      hiding (_/→1_) renaming (_/→*_ to _/→v*_; _/↔_ to _/≡v_)

  -- Term substitutions in reductions/equivalences.
  module CbvSubstitution where
    open Substitution Sort
      using (termSubst; weaken; sub-commutes; varLiftSubLemmas)

    -- Application of renamings to reductions/equivalences.
    varSubstApp : CbvSubstApp (TermSubst.varLift termSubst)
    varSubstApp = record { /-sub-↑ = /-sub-↑ }
      where open LiftSubLemmas varLiftSubLemmas
    private module V = CbvSubstApp varSubstApp

    -- Weakening of one-step CBV reductions.
    weaken-→v : ∀ {n} {a b : Term n} → a →v b → weaken a →v weaken b
    weaken-→v a→b = a→b V./→v VarSubst.wk

    -- Weakening of CBV reductions.
    weaken-→v* : ∀ {n} {a b : Term n} → a →v* b → weaken a →v* weaken b
    weaken-→v* = gmap weaken weaken-→v

    -- Weakening of equivalences.
    weaken-≡v : ∀ {n} {a b : Term n} → a ≡v b → weaken a ≡v weaken b
    weaken-≡v = EqClos.gmap weaken weaken-→v

    -- Application of term substitutions to reductions/equivalences.
    termSubstApp : CbvSubstApp (TermSubst.termLift termSubst)
    termSubstApp = record { /-sub-↑ = λ a _ _ → sub-commutes a }
    open CbvSubstApp termSubstApp public


  ----------------------------------------------------------------------
  -- Properties of the CBV reductions/equivalence

  -- Inclusions.
  →v⇒→v* = →1⇒→* reduction
  →v*⇒≡v = →*⇒↔  reduction
  →v⇒≡v  = →1⇒↔  reduction

  -- CBV reduction is a preorder.
  →v*-predorder = →*-predorder reduction

  -- Preorder reasoning for CBV reduction.
  module →v*-Reasoning = →*-Reasoning reduction

  -- Terms together with CBV equivalence form a setoid.
  ≡v-setoid = ↔-setoid reduction

  -- Equational reasoning for CBV equivalence.
  module ≡v-Reasoning = ↔-Reasoning reduction


  ----------------------------------------------------------------------
  -- Relationships between CBV reduction and full β-reduction

  -- One-step CBV reduction implies one-step β-reduction.
  →v⇒→β : ∀ {n} {a b : Term n} → a →v b → a →β b
  →v⇒→β (cont a b c) = cont a b _
  →v⇒→β (a₁→a₂ ·₁ b) = →v⇒→β a₁→a₂ ·₁ b
  →v⇒→β (a ·₂ b₁→b₂) = _ ·₂ →v⇒→β b₁→b₂

  -- CBV reduction implies parallel reduction.
  →v*⇒→β* : ∀ {n} {a b : Term n} → a →v* b → a →β* b
  →v*⇒→β* = map →v⇒→β

  -- CBV equivalence implies parallel equivalence.
  ≡v⇒≡p : ∀ {n} {a b : Term n} → a ≡v b → a ≡β b
  ≡v⇒≡p = EqClos.map →v⇒→β
