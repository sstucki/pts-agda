------------------------------------------------------------------------
-- Syntax of pure type systems (PTS)
------------------------------------------------------------------------

module Pts.Syntax where

open import Data.Fin using (Fin)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Fin.Substitution.Typed
open import Data.Star using (Star; ε; _◅_)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Vec using (lookup)
open import Relation.Binary.PropositionalEquality as PropEq
open PropEq.≡-Reasoning


-- All submodules are parametrized by a given set of sorts.
module _ (Sort : Set) where

  ----------------------------------------------------------------------
  -- Abstract syntax of terms

  module Syntax where

    infixl 9 _·_

    -- Untyped terms with up to n free variables.
    data Term (n : ℕ) : Set where
      var  : (x : Fin n)                     → Term n  -- variable
      sort : (s : Sort)                      → Term n  -- sort
      Π    : (a : Term n) (b : Term (1 + n)) → Term n  -- dependent product
      ƛ    : (a : Term n) (b : Term (1 + n)) → Term n  -- abstraction
      _·_  : (a b : Term n)                  → Term n  -- application

  open Syntax

  ----------------------------------------------------------------------
  -- Substitutions in terms

  -- Application of generic substitutions to terms
  module SubstApp {T} (l : Lift T Term) where
    open Lift l

    infixl 8 _/_

    -- Apply a substitution to a term.
    _/_ : ∀ {m n} → Term m → Sub T m n → Term n
    var x  / σ = lift (lookup x σ)
    sort s / σ = sort s
    Π a b  / σ = Π (a / σ) (b / σ ↑)
    ƛ a b  / σ = ƛ (a / σ) (b / σ ↑)
    a · b  / σ = (a / σ) · (b / σ)

    -- Some helper lemmas about applying sequences of substitutions.
    -- To be used in PathSubstLemmas.

    open Application (record { _/_ = _/_ }) hiding (_/_)

    -- Sorts are invariant under substitution.
    sort-/✶-↑✶ : ∀ k {m n s} (σs : Subs T m n) → sort s /✶ σs ↑✶ k ≡ sort s
    sort-/✶-↑✶ k ε        = refl
    sort-/✶-↑✶ k (σ ◅ σs) = cong₂ _/_ (sort-/✶-↑✶ k σs) refl

    -- Substitutions in dependent product types are compositional.
    Π-/✶-↑✶ : ∀ k {m n a b} (σs : Subs T m n) →
                  (Π a b) /✶ σs ↑✶ k ≡  Π (a /✶ σs ↑✶ k) (b /✶ σs ↑✶ suc k)
    Π-/✶-↑✶ k ε        = refl
    Π-/✶-↑✶ k (σ ◅ σs) = cong₂ _/_ (Π-/✶-↑✶ k σs) refl

    -- Substitutions in abstractions are compositional.
    ƛ-/✶-↑✶ : ∀ k {m n a b} (σs : Subs T m n) →
                  (ƛ a b) /✶ σs ↑✶ k ≡  ƛ (a /✶ σs ↑✶ k) (b /✶ σs ↑✶ suc k)
    ƛ-/✶-↑✶ k ε        = refl
    ƛ-/✶-↑✶ k (σ ◅ σs) = cong₂ _/_ (ƛ-/✶-↑✶ k σs) refl

    -- Substitutions in applications are compositional.
    ·-/✶-↑✶ : ∀ k {m n a b} (σs : Subs T m n) →
                  (a · b) /✶ σs ↑✶ k ≡ (a /✶ σs ↑✶ k) · (b /✶ σs ↑✶ k)
    ·-/✶-↑✶ k ε        = refl
    ·-/✶-↑✶ k (σ ◅ σs) = cong₂ _/_ (·-/✶-↑✶ k σs) refl

  -- Substitutions in terms and associated lemmas.
  module Substitution where

    -- Term substitutions.
    termSubst : TermSubst Term
    termSubst = record { var = var; app = SubstApp._/_ }

    -- Lemmas relating application of sequences of generic substitutions
    -- lifted to any number of additional variables.
    --
    -- Using these generic lemmas, we can instantiate the record
    -- Data.Fin.Substitution.Lemmas.TermLemmas below, which gives access
    -- to a number of useful (derived) lemmas about path substitutions.
    module Lemmas {T₁ T₂} {lift₁ : Lift T₁ Term} {lift₂ : Lift T₂ Term} where
      open SubstApp
      open Lift lift₁ using () renaming (_↑✶_ to _↑✶₁_)
      open Lift lift₂ using () renaming (_↑✶_ to _↑✶₂_)
      open Application (record { _/_ = SubstApp._/_ lift₁ }) using ()
        renaming (_/✶_ to _/✶₁_)
      open Application (record { _/_ = SubstApp._/_ lift₂ }) using ()
        renaming (_/✶_ to _/✶₂_)

      -- Sequences of (lifted) T₁ and T₂-substitutions are equivalent
      -- when applied to terms if they are equivalent when applied to
      -- variables.
      /✶-↑✶ : ∀ {m n} (σs₁ : Subs T₁ m n) (σs₂ : Subs T₂ m n) →
                (∀ k x → var x /✶₁ σs₁ ↑✶₁ k ≡ var x /✶₂ σs₂ ↑✶₂ k) →
                 ∀ k t → t     /✶₁ σs₁ ↑✶₁ k ≡ t     /✶₂ σs₂ ↑✶₂ k
      /✶-↑✶ σs₁ σs₂ hyp k (var x)  = hyp k x
      /✶-↑✶ σs₁ σs₂ hyp k (sort s) = begin
        sort s /✶₁ σs₁ ↑✶₁ k   ≡⟨ sort-/✶-↑✶ _ k σs₁ ⟩
        sort s                 ≡⟨ sym (sort-/✶-↑✶ _ k σs₂) ⟩
        sort s /✶₂ σs₂ ↑✶₂ k   ∎
      /✶-↑✶ σs₁ σs₂ hyp k (Π a b) = begin
          (Π a b) /✶₁ σs₁ ↑✶₁ k
        ≡⟨ Π-/✶-↑✶ _ k σs₁ ⟩
          Π (a /✶₁ σs₁ ↑✶₁ k) (b /✶₁ σs₁ ↑✶₁ suc k)
        ≡⟨ cong₂ Π (/✶-↑✶ σs₁ σs₂ hyp k a) (/✶-↑✶ σs₁ σs₂ hyp (suc k) b) ⟩
          Π (a /✶₂ σs₂ ↑✶₂ k) (b /✶₂ σs₂ ↑✶₂ suc k)
        ≡⟨ sym (Π-/✶-↑✶ _ k σs₂) ⟩
          (Π a b) /✶₂ σs₂ ↑✶₂ k
        ∎
      /✶-↑✶ σs₁ σs₂ hyp k (ƛ a b) = begin
          (ƛ a b) /✶₁ σs₁ ↑✶₁ k
        ≡⟨ ƛ-/✶-↑✶ _ k σs₁ ⟩
          ƛ (a /✶₁ σs₁ ↑✶₁ k) (b /✶₁ σs₁ ↑✶₁ suc k)
        ≡⟨ cong₂ ƛ (/✶-↑✶ σs₁ σs₂ hyp k a) (/✶-↑✶ σs₁ σs₂ hyp (suc k) b) ⟩
          ƛ (a /✶₂ σs₂ ↑✶₂ k) (b /✶₂ σs₂ ↑✶₂ suc k)
        ≡⟨ sym (ƛ-/✶-↑✶ _ k σs₂) ⟩
          (ƛ a b) /✶₂ σs₂ ↑✶₂ k
        ∎
      /✶-↑✶ σs₁ σs₂ hyp k (a · b) = begin
          (a · b) /✶₁ σs₁ ↑✶₁ k
        ≡⟨ ·-/✶-↑✶ _ k σs₁ ⟩
          (a /✶₁ σs₁ ↑✶₁ k) · (b /✶₁ σs₁ ↑✶₁ k)
        ≡⟨ cong₂ _·_ (/✶-↑✶ σs₁ σs₂ hyp k a) (/✶-↑✶ σs₁ σs₂ hyp k b) ⟩
          (a /✶₂ σs₂ ↑✶₂ k) · (b /✶₂ σs₂ ↑✶₂ k)
        ≡⟨ sym (·-/✶-↑✶ _ k σs₂) ⟩
          (a · b) /✶₂ σs₂ ↑✶₂ k
        ∎

    -- By instantiating TermLemmas, we get access to a number of useful
    -- (derived) lemmas about path substitutions.
    termLemmas : TermLemmas Term
    termLemmas = record
      { termSubst = termSubst
      ; app-var   = refl
      ; /✶-↑✶     = Lemmas./✶-↑✶
      }

    open TermLemmas termLemmas public hiding (var; termSubst)

    -- By instantiating TermLikeLemmas, we get access to a number of
    -- useful (derived) lemmas about variable substitutions (renamings).
    private
      termLikeLemmas : TermLikeLemmas Term Term
      termLikeLemmas = record
        { app        = SubstApp._/_
        ; termLemmas = termLemmas
        ; /✶-↑✶₁     = Lemmas./✶-↑✶
        ; /✶-↑✶₂     = Lemmas./✶-↑✶
        }

    open TermLikeLemmas termLikeLemmas public
      using (varLiftAppLemmas; varLiftSubLemmas; _/Var_)

    infix 10 _[_]

    -- Shorthand for single-variable term substitutions.
    _[_] : ∀ {n} → Term (1 + n) → Term n → Term n
    a [ b ] = a / sub b


  ----------------------------------------------------------------------
  -- Concrete typing contexts over terms.

  module Ctx where
    open Substitution using (weaken)
    open Context      Term public hiding (module Ctx)

    weakenOps : WeakenOps
    weakenOps = record { weaken = weaken }

    open WeakenOps weakenOps public hiding (weaken)
