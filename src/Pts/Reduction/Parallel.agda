------------------------------------------------------------------------
-- Parallel reduction in pure type systems (PTS)
------------------------------------------------------------------------

module Pts.Reduction.Parallel where

open import Data.Fin using (Fin)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Fin.Substitution.Relation
open import Data.Star using (Star; ε; _◅_; _◅◅_)
open import Data.Product using (_,_; ∃; _×_)
open import Data.Nat using (ℕ; _+_)
open import Data.Vec.All using (lookup₂)
import Function as Fun
open import Relation.Binary
open import Relation.Binary.EquivalenceClosure using (EqClosure)
open import Relation.Binary.SymmetricClosure using (fwd; bwd)
open import Relation.Binary.Reduction
import Relation.Binary.PropositionalEquality as P

open import Pts.Syntax

-- All remaining submodules are parametrized by a given set of sorts.
module _ {Sort : Set} where
  open Syntax       Sort
  open Substitution Sort using (_[_])

  ----------------------------------------------------------------------
  -- Parallel reduction

  infixl 9 _·_
  infix  5 _⇛_

  -- One-step parallel reduction.
  data _⇛_ {n : ℕ} : Term n → Term n → Set where
    refl : ∀ {a}                                 →       a ⇛ a
    Π    : ∀ {a₁ a₂ b₁ b₂}   → a₁ ⇛ a₂ → b₁ ⇛ b₂ → Π a₁ b₁ ⇛ Π a₂ b₂
    ƛ    : ∀ {a₁ a₂ b₁ b₂}   → a₁ ⇛ a₂ → b₁ ⇛ b₂ → ƛ a₁ b₁ ⇛ ƛ a₂ b₂
    _·_  : ∀ {a₁ a₂ b₁ b₂}   → a₁ ⇛ a₂ → b₁ ⇛ b₂ → a₁ · b₁ ⇛ a₂ · b₂
    cont : ∀ {a b₁ b₂ c₁ c₂} → b₁ ⇛ b₂ → c₁ ⇛ c₂ →
           (ƛ a b₁) · c₁ ⇛ b₂ [ c₂ ]

  reduction : Reduction Term
  reduction = record { _→1_ = _⇛_ }

  -- Parallel reduction and equivalence.
  open Reduction reduction public renaming (_→*_ to _⇛*_; _↔_ to _≡p_)


  ----------------------------------------------------------------------
  -- Simple properties of parallel reduction

  -- Inclusions.
  ⇛⇒⇛*  = →1⇒→* reduction
  ⇛*⇒≡p = →*⇒↔  reduction
  ⇛⇒≡p  = →1⇒↔  reduction

  -- parallel reduction is a preorder.
  ⇛*-predorder = →*-predorder reduction

  -- Terms together with parallel equivalence form a setoid.
  ≡p-setoid = ↔-setoid reduction

  open P using (_≡_)

  -- Shapes are preserved by one-step parallel reduction.

  sort-⇛ : ∀ {n s} {a : Term n} → sort s ⇛ a → sort s ≡ a
  sort-⇛ refl = P.refl

  ƛ-⇛ : ∀ {n} {a : Term n} {b c} → ƛ a b ⇛ c →
        ∃ λ a′ → ∃ λ b′ → a ⇛ a′ × b ⇛ b′ × ƛ a′ b′ ≡ c
  ƛ-⇛ refl          = _ , _ , refl , refl , P.refl
  ƛ-⇛ (ƛ a⇛a′ b⇛b′) = _ , _ , a⇛a′ , b⇛b′ , P.refl

  Π-⇛ : ∀ {n} {a : Term n} {b c} → Π a b ⇛ c →
        ∃ λ a′ → ∃ λ b′ → a ⇛ a′ × b ⇛ b′ × Π a′ b′ ≡ c
  Π-⇛ refl          = _ , _ , refl , refl , P.refl
  Π-⇛ (Π a⇛a′ b⇛b′) = _ , _ , a⇛a′ , b⇛b′ , P.refl

  -- Shapes are preserved by parallel reduction.

  sort-⇛* : ∀ {n s} {a : Term n} → sort s ⇛* a → sort s ≡ a
  sort-⇛* ε             = P.refl
  sort-⇛* (refl ◅ s⇛*b) = sort-⇛* s⇛*b

  ƛ-⇛* : ∀ {n} {a : Term n} {b c} → ƛ a b ⇛* c →
         ∃ λ a′ → ∃ λ b′ → a ⇛* a′ × b ⇛* b′ × ƛ a′ b′ ≡ c
  ƛ-⇛* ε                        = _ , _ , ε , ε , P.refl
  ƛ-⇛* (refl        ◅ λab⇛*d)   = ƛ-⇛* λab⇛*d
  ƛ-⇛* (ƛ a⇛a₁ b⇛b₁ ◅ λa₁b₁⇛*d) =
    let a₂ , b₂ , a₁⇛*a₂ , b₁⇛*b₂ , λa₂b₂≡d = ƛ-⇛* λa₁b₁⇛*d
    in a₂ , b₂ , a⇛a₁ ◅ a₁⇛*a₂ , b⇛b₁ ◅ b₁⇛*b₂ , λa₂b₂≡d

  Π-⇛* : ∀ {n} {a : Term n} {b c} → Π a b ⇛* c →
         ∃ λ a′ → ∃ λ b′ → a ⇛* a′ × b ⇛* b′ × Π a′ b′ ≡ c
  Π-⇛* ε                        = _ , _ , ε , ε , P.refl
  Π-⇛* (refl        ◅ Πab⇛*d)   = Π-⇛* Πab⇛*d
  Π-⇛* (Π a⇛a₁ b⇛b₁ ◅ Πa₁b₁⇛*d) =
    let a₂ , b₂ , a₁⇛*a₂ , b₁⇛*b₂ , Πa₂b₂≡d = Π-⇛* Πa₁b₁⇛*d
    in a₂ , b₂ , a⇛a₁ ◅ a₁⇛*a₂ , b⇛b₁ ◅ b₁⇛*b₂ , Πa₂b₂≡d


  ----------------------------------------------------------------------
  -- Substitutions lifted to parallel reduction
  --
  -- The application _/⇛_ below may be considered a substitution
  -- lemma, i.e. it establishes that substitutions of terms preserve
  -- parallel reduction:
  --
  --                                ⇛
  --                           a ------→ b
  --                           |         |
  --                       -/σ |         | -/σ
  --                           ↓    ⇛    ↓
  --                          a/σ ····→ b/σ
  --
  -- ∀ (a b : Term n) (σ : Sub Term m n).

  -- Application of generic substitutions lifted to reduction.
  record ParSubstApp {T₁ T₂} (R : TermRel T₁ T₂)
                     (l₁ : Lift T₁ Term) (l₂ : Lift T₂ Term)
                     (rl : RelLift R _⇛_ l₁ l₂) : Set where
    infix  10 _↑₂
    infixl 8  _/₁_ _/₂_ _/_ _/⇛_

    open Substitution Sort using (termSubst)
    private
      _/₁_ = TermSubst.app termSubst l₁
      _/₂_ = TermSubst.app termSubst l₂
      _↑₂  = Lift._↑ l₂
    open LiftTermRel T₁ T₂ using (_⟨_⟩_)
    open RelLift rl
    open P using (sym; subst)

    -- T₂-substitutions commute.
    field /₂-sub-↑ : ∀ {m n b} {σ : Sub T₂ m n} a →
                     (a [ b ]) /₂ σ ≡ (a /₂ (σ ↑₂)) [ b /₂ σ ]

    _/_ : ∀ {m n} {σ₁ : Sub T₁ m n} {σ₂ : Sub T₂ m n} →
          ∀ a → σ₁ ⟨ R ⟩ σ₂ → a /₁ σ₁ ⇛ a /₂ σ₂
    var x   / σ₁∼σ₂ = lift (lookup₂ x σ₁∼σ₂)
    sort s  / σ₁∼σ₂ = refl
    Π a b   / σ₁∼σ₂ = Π (a / σ₁∼σ₂) (b / σ₁∼σ₂ ↑)
    ƛ a b   / σ₁∼σ₂ = ƛ (a / σ₁∼σ₂) (b / σ₁∼σ₂ ↑)
    (a · b) / σ₁∼σ₂ = (a / σ₁∼σ₂) · (b / σ₁∼σ₂)

    _/⇛_ : ∀ {m n a₁ a₂} {σ₁ : Sub T₁ m n} {σ₂ : Sub T₂ m n} →
           a₁ ⇛ a₂ → σ₁ ⟨ R ⟩ σ₂ → a₁ /₁ σ₁ ⇛ a₂ /₂ σ₂
    refl {a}      /⇛ σ₁∼σ₂ = a / σ₁∼σ₂
    Π a₁⇛a₂ b₁⇛b₂ /⇛ σ₁∼σ₂ = Π (a₁⇛a₂ /⇛ σ₁∼σ₂) (b₁⇛b₂ /⇛ σ₁∼σ₂ ↑)
    ƛ a₁⇛a₂ b₁⇛b₂ /⇛ σ₁∼σ₂ = ƛ (a₁⇛a₂ /⇛ σ₁∼σ₂) (b₁⇛b₂ /⇛ σ₁∼σ₂ ↑)
    a₁⇛a₂ · b₁⇛b₂ /⇛ σ₁∼σ₂ = (a₁⇛a₂ /⇛ σ₁∼σ₂) · (b₁⇛b₂ /⇛ σ₁∼σ₂)
    cont {b₂ = b₂} a₁⇛a₂ b₁⇛b₂ /⇛ σ₁∼σ₂ =
      P.subst (_⇛_ _) (sym (/₂-sub-↑ b₂))
                   (cont (a₁⇛a₂ /⇛ σ₁∼σ₂ ↑) (b₁⇛b₂ /⇛ σ₁∼σ₂))

  -- Term substitutions lifted to parallel reduction.
  module ParSubstitution where
    open Substitution Sort using (termSubst; sub-commutes; varLiftSubLemmas)
    open P using (_≡_; refl)
    private
      module S = TermSubst termSubst
      module V = VarEqSubst

    varLift : RelLift _≡_ _⇛_ S.varLift S.varLift
    varLift = record { simple = V.simple; lift = lift }
      where
        lift : ∀ {n} {x₁ x₂ : Fin n} → x₁ ≡ x₂ → S.var x₁ ⇛ S.var x₂
        lift {x₁ = x} refl = refl

    varSubstApp : ParSubstApp _≡_ S.varLift S.varLift varLift
    varSubstApp = record { /₂-sub-↑ = λ a → /-sub-↑ a _ _ }
      where open LiftSubLemmas varLiftSubLemmas

    infix 8 _/Var-⇛_

    _/Var-⇛_ : ∀ {m n a₁ a₂} {σ₁ σ₂ : Sub Fin m n} →
               a₁ ⇛ a₂ → σ₁ V.⟨≡⟩ σ₂ → (a₁ S./Var σ₁) ⇛ (a₂ S./Var σ₂)
    _/Var-⇛_ = ParSubstApp._/⇛_ varSubstApp

    simple : RelSimple _⇛_ S.simple S.simple
    simple = record
      { extension = record { weaken = λ t₁⇛t₂ → t₁⇛t₂ /Var-⇛ V.wk }
      ; var       = λ x → refl {a = var x}
      }

    termLift : RelLift _⇛_ _⇛_ S.termLift S.termLift
    termLift = record { simple = simple; lift = Fun.id }

    termSubstApp : ParSubstApp _⇛_ S.termLift S.termLift termLift
    termSubstApp = record { /₂-sub-↑ = sub-commutes }

    open ParSubstApp termSubstApp public

    subst : RelSubst _⇛_ S.subst S.subst
    subst = record
      { simple      = simple
      ; application = record { _/_ = _/⇛_ }
      }

    open LiftTermRel Term Term public using (_⟨_⟩_)
    open RelSubst subst public hiding (var; simple; _/_)

    infix 10 _[⇛_]

    -- Shorthand for single-variable substitutions lifted to redcution.
    _[⇛_] : ∀ {n} {a₁ : Term (1 + n)} {a₂} {b₁ : Term n} {b₂} →
            a₁ ⇛ a₂ → b₁ ⇛ b₂ → a₁ S./ S.sub b₁ ⇛ a₂ S./ S.sub b₂
    a₁⇛a₂ [⇛ b₁⇛b₂ ] = a₁⇛a₂ /⇛ sub b₁⇛b₂

  open ParSubstitution


  ----------------------------------------------------------------------
  -- Confluence of parallel reduction
  --
  -- Parallel reduction enjoys the single-step diamond property,
  -- i.e. for any pair a ⇛ b₁, a ⇛ b₂ of parallel reductions, there is
  -- a term c, such that
  --
  --                                ⇛
  --                           a ------→ b₂
  --                           |         :
  --                         ⇛ |         : ⇛
  --                           ↓    ⇛    ↓
  --                           b₁ ·····→ c
  --
  -- commutes.  Confluence (aka the Church-Rosser property) then
  -- follows by pasting of diagrams.

  infixl 4 _⋄_

  -- Diamond property of one-step reduction.
  _⋄_ : ∀ {n} {a b₁ b₂ : Term n} → a ⇛ b₁ → a ⇛ b₂ → ∃ λ c → b₁ ⇛ c × b₂ ⇛ c
  refl ⋄ a⇛b  = _ , a⇛b  , refl
  a⇛b  ⋄ refl = _ , refl , a⇛b
  Π a₁⇛b₁₁ a₂⇛b₁₂ ⋄ Π a₁⇛b₂₁ a₂⇛b₂₂ =
    let c₁ , b₁₁⇛c₁ , b₂₁⇛c₁ = a₁⇛b₁₁ ⋄ a₁⇛b₂₁
        c₂ , b₁₂⇛c₂ , b₂₂⇛c₂ = a₂⇛b₁₂ ⋄ a₂⇛b₂₂
    in Π c₁ c₂ , Π b₁₁⇛c₁ b₁₂⇛c₂ , Π b₂₁⇛c₁ b₂₂⇛c₂
  ƛ a₁⇛b₁₁ a₂⇛b₁₂ ⋄ ƛ a₁⇛b₂₁ a₂⇛b₂₂ =
    let c₁ , b₁₁⇛c₁ , b₂₁⇛c₁ = a₁⇛b₁₁ ⋄ a₁⇛b₂₁
        c₂ , b₁₂⇛c₂ , b₂₂⇛c₂ = a₂⇛b₁₂ ⋄ a₂⇛b₂₂
    in ƛ c₁ c₂ , ƛ b₁₁⇛c₁ b₁₂⇛c₂ , ƛ b₂₁⇛c₁ b₂₂⇛c₂
  a₁⇛b₁₁ · a₂⇛b₁₂ ⋄ a₁⇛b₂₁ · a₂⇛b₂₂ =
    let c₁ , b₁₁⇛c₁ , b₂₁⇛c₁ = a₁⇛b₁₁ ⋄ a₁⇛b₂₁
        c₂ , b₁₂⇛c₂ , b₂₂⇛c₂ = a₂⇛b₁₂ ⋄ a₂⇛b₂₂
    in c₁ · c₂ , b₁₁⇛c₁ · b₁₂⇛c₂ , b₂₁⇛c₁ · b₂₂⇛c₂
  refl · a₂⇛b₁₂ ⋄ cont {b₂ = b₂₁} a₁⇛b₂₁ a₂⇛b₂₂ =
    let c₂ , b₁₂⇛c₂ , b₂₂⇛c₂ = a₂⇛b₁₂ ⋄ a₂⇛b₂₂
    in b₂₁ [ c₂ ] , cont a₁⇛b₂₁ b₁₂⇛c₂ , refl {a = b₂₁} [⇛ b₂₂⇛c₂ ]
  ƛ _ a₁⇛b₁₁ · a₂⇛b₁₂ ⋄ cont a₁⇛b₂₁ a₂⇛b₂₂ =
    let c₁ , b₁₁⇛c₁ , b₂₁⇛c₁ = a₁⇛b₁₁ ⋄ a₁⇛b₂₁
        c₂ , b₁₂⇛c₂ , b₂₂⇛c₂ = a₂⇛b₁₂ ⋄ a₂⇛b₂₂
    in c₁ [ c₂ ] , cont b₁₁⇛c₁ b₁₂⇛c₂ , b₂₁⇛c₁ [⇛ b₂₂⇛c₂ ]
  cont {b₂ = b₁₁} a₁⇛b₁₁ a₂⇛b₁₂ ⋄ refl · a₂⇛b₂₂ =
    let c₂ , b₁₂⇛c₂ , b₂₂⇛c₂ = a₂⇛b₁₂ ⋄ a₂⇛b₂₂
    in b₁₁ [ c₂ ] , refl {a = b₁₁} [⇛ b₁₂⇛c₂ ] , cont a₁⇛b₁₁ b₂₂⇛c₂
  cont a₁⇛b₁₁ a₂⇛b₁₂ ⋄ ƛ _ a₁⇛b₂₁ · a₂⇛b₂₂ =
    let c₁ , b₁₁⇛c₁ , b₂₁⇛c₁ = a₁⇛b₁₁ ⋄ a₁⇛b₂₁
        c₂ , b₁₂⇛c₂ , b₂₂⇛c₂ = a₂⇛b₁₂ ⋄ a₂⇛b₂₂
    in c₁ [ c₂ ] , b₁₁⇛c₁ [⇛ b₁₂⇛c₂ ] , cont b₂₁⇛c₁ b₂₂⇛c₂
  cont a₁⇛b₁₁ a₂⇛b₁₂ ⋄ cont a₁⇛b₂₁ a₂⇛b₂₂ =
    let c₁ , b₁₁⇛c₁ , b₂₁⇛c₁ = a₁⇛b₁₁ ⋄ a₁⇛b₂₁
        c₂ , b₁₂⇛c₂ , b₂₂⇛c₂ = a₂⇛b₁₂ ⋄ a₂⇛b₂₂
    in c₁ [ c₂ ] , b₁₁⇛c₁ [⇛ b₁₂⇛c₂ ] , b₂₁⇛c₁ [⇛ b₂₂⇛c₂ ]

  -- A strip lemma.
  _⋄′_ : ∀ {n} {a b₁ b₂ : Term n} →
         a ⇛ b₁ → a ⇛* b₂ → ∃ λ c → b₁ ⇛* c × b₂ ⇛ c
  a⇛b  ⋄′ ε               = _ , ε , a⇛b
  a⇛b₁ ⋄′ (a⇛b₂ ◅ b₂⇛*c₂) =
    let c₁ , b₁⇛c₁ , b₂⇛c₁ = a⇛b₁ ⋄ a⇛b₂
        d  , c₁⇛*d , c₂⇛d  = b₂⇛c₁ ⋄′ b₂⇛*c₂
    in d , b₁⇛c₁ ◅ c₁⇛*d , c₂⇛d

  -- Confluence (aka the Church-Rosser property) of _⇛*_
  _⋄*_ : ∀ {n} {a b₁ b₂ : Term n} →
         a ⇛* b₁ → a ⇛* b₂ → ∃ λ c → b₁ ⇛* c × b₂ ⇛* c
  ε               ⋄* a⇛*b  = _ , a⇛*b , ε
  (a⇛b₁ ◅ b₁⇛*c₁) ⋄* a⇛*b₂ =
    let c₂ , b₁⇛*c₂ , b₂⇛c₂ = a⇛b₁ ⋄′ a⇛*b₂
        d  , c₁⇛*d  , c₂⇛*d = b₁⇛*c₁ ⋄* b₁⇛*c₂
    in d , c₁⇛*d , b₂⇛c₂ ◅ c₂⇛*d

  -- Factorization of equivalence into parallel reductions.
  ≡p⇒⇛* : ∀ {n} {a b : Term n} → a ≡p b → ∃ λ c → a ⇛* c × b ⇛* c
  ≡p⇒⇛* ε               = _ , ε , ε
  ≡p⇒⇛* (fwd a⇛b ◅ b≡c) =
    let d , b⇛*d , c⇛*d = ≡p⇒⇛* b≡c in d , a⇛b ◅ b⇛*d , c⇛*d
  ≡p⇒⇛* (bwd a⇚b ◅ b≡c) =
    let d , b⇛*d , c⇛*d = ≡p⇒⇛* b≡c
        e , a⇛*e , d⇛e  = a⇚b ⋄′ b⇛*d
    in e , a⇛*e , c⇛*d ◅◅ (d⇛e ◅ ε)

  -- Π-injectivity (with respect to ≡p).
  Π-inj : ∀ {n} {a₁ a₂ : Term n} {b₁ b₂} → Π a₁ b₁ ≡p Π a₂ b₂ →
          a₁ ≡p a₂ × b₁ ≡p b₂
  Π-inj Πa₁b₁≡Πa₂b₂ with ≡p⇒⇛* Πa₁b₁≡Πa₂b₂
  Π-inj Πa₁b₁≡Πa₂b₂ | c , Πa₁b₁⇛*c , Πa₂b₂⇛*c with
    Π-⇛* Πa₁b₁⇛*c | Π-⇛* Πa₂b₂⇛*c
  Π-inj Πa₁b₁≡Πa₂b₂ | Π a₃ b₃ , Πa₁b₁⇛*c , Πa₂b₂⇛*c |
    ._ , ._ , a₁⇛*a₃ , b₁⇛*b₃ , P.refl | ._ , ._ , a₂⇛*a₃ , b₂⇛*b₃ , P.refl =
    ⇛*⇒≡p a₁⇛*a₃ ◅◅ sym (⇛*⇒≡p a₂⇛*a₃) , ⇛*⇒≡p b₁⇛*b₃ ◅◅ sym (⇛*⇒≡p b₂⇛*b₃)
    where
      module ParSetoid {n} where
        open Setoid (≡p-setoid {n}) public
      open ParSetoid

  -- Parallel equivalence on sorts implies syntactic equivalence.
  sort-≡p : ∀ {n s₁ s₂} → sort {n} s₁ ≡p sort s₂ → s₁ ≡ s₂
  sort-≡p s₁≡s₂ with ≡p⇒⇛* s₁≡s₂
  sort-≡p s₁≡s₂ | c , s₁⇛*c , s₂⇛*c with sort-⇛* s₁⇛*c | sort-⇛* s₂⇛*c
  sort-≡p s₁≡s₂ | ._ , s₁⇛*c , s₂⇛*c | P.refl | P.refl = P.refl
