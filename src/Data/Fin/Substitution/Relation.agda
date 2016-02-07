------------------------------------------------------------------------
-- Binary relations lifted to substitutions
------------------------------------------------------------------------

module Data.Fin.Substitution.Relation where

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec.All using (All₂; []; _∷_; lookup₂)
open import Data.Vec.All.Properties using (gmap₂)
import Function as Fun
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)


-- Term relations.
--
-- A term relation R : TermRel T₁ T₂ is a ℕ-indexed family of binary
-- relations relating T₁-terms to T₂-terms.
TermRel : (ℕ → Set) → (ℕ → Set) → Set₁
TermRel T₁ T₂ = ∀ {n} → T₁ n → T₂ n → Set

-- Substitution relations.
--
-- A substitution relation R : SubRel T₁ T₂ is a ℕ²-indexed family
-- of binary relations relating T₁-substitutions to T₂-substitutions.
SubRel : (ℕ → Set) → (ℕ → Set) → Set₁
SubRel T₁ T₂ = ∀ {m n} → Sub T₁ m n → Sub T₂ m n → Set

module LiftTermRel (T₁ T₂ : ℕ → Set) where

  -- Term relations lifted point-wise to corresponding substitutions.
  --
  -- Given a relation R on T₁ and T₂ terms, the family of relations
  -- (lift R) relates T₁ and T₂ substitutions point-wise.
  lift : TermRel T₁ T₂ → SubRel T₁ T₂
  lift P σ₁ σ₂ = All₂ P σ₁ σ₂

  infix 4 _⟨_⟩_

  -- Syntactic sugar: and infix version of lifting.
  _⟨_⟩_ : ∀ {m n} → Sub T₁ m n → TermRel T₁ T₂ → Sub T₂ m n → Set
  σ₁ ⟨ R ⟩ σ₂ = lift R σ₁ σ₂


------------------------------------------------------------------------
-- Generic substitutions lifted to relations

module _ {T₁ T₂} (_∼_ : TermRel T₁ T₂) where
  open LiftTermRel T₁ T₂ using (_⟨_⟩_)

  -- Extensions of substitutions lifted to relations.
  record RelExtension (ext₁ : Extension T₁) (ext₂ : Extension T₂) : Set where
    private
      module E₁  = Extension ext₁
      module E₂  = Extension ext₂

    -- Weakening lifted to _∼_.
    field weaken : ∀ {n} {t₁ : T₁ n} {t₂ : T₂ n} →
                   t₁ ∼ t₂ → E₁.weaken t₁ ∼ E₂.weaken t₂

    infixr 5 _/∷_

    -- Extension.
    _/∷_ : ∀ {m n t₁ t₂} {σ₁ : Sub T₁ m n} {σ₂ : Sub T₂ m n} →
           t₁ ∼ t₂ → σ₁ ⟨ _∼_ ⟩ σ₂ → t₁ E₁./∷ σ₁ ⟨ _∼_ ⟩ t₂ E₂./∷ σ₂
    t₁∼t₂ /∷ σ₁∼σ₂ = t₁∼t₂ ∷ gmap₂ weaken σ₁∼σ₂

  -- Simple substitutions lifted to relations.
  record RelSimple (simple₁ : Simple T₁) (simple₂ : Simple T₂) : Set where
    private
      module S₁ = SimpleExt simple₁
      module S₂ = SimpleExt simple₂

    field
      extension : RelExtension S₁.extension S₂.extension

      -- Relates variables.
      var : ∀ {n} (x : Fin n) → S₁.var x ∼ S₂.var x

    open RelExtension extension public

    infix  10 _↑
    infixl 10 _↑⋆_

    -- Lifting.

    _↑ : ∀ {m n} {σ₁ : Sub T₁ m n} {σ₂ : Sub T₂ m n} →
         σ₁ ⟨ _∼_ ⟩ σ₂ → σ₁ S₁.↑ ⟨ _∼_ ⟩ σ₂ S₂.↑
    σ₁∼σ₂ ↑ = var zero /∷ σ₁∼σ₂

    _↑⋆_ : ∀ {m n} {σ₁ : Sub T₁ m n} {σ₂ : Sub T₂ m n} →
           σ₁ ⟨ _∼_ ⟩ σ₂ → ∀ k → σ₁ S₁.↑⋆ k ⟨ _∼_ ⟩ σ₂ S₂.↑⋆ k
    σ₁∼σ₂ ↑⋆ zero  = σ₁∼σ₂
    σ₁∼σ₂ ↑⋆ suc k = (σ₁∼σ₂ ↑⋆ k) ↑

    -- The identity substitution.
    id : ∀ {n} → S₁.id {n} ⟨ _∼_ ⟩ S₂.id {n}
    id {zero}  = []
    id {suc n} = id ↑

    -- Weakening.

    wk⋆ : ∀ k {n} → S₁.wk⋆ k {n} ⟨ _∼_ ⟩ S₂.wk⋆ k {n}
    wk⋆ zero    = id
    wk⋆ (suc k) = gmap₂ weaken (wk⋆ k)

    wk : ∀ {n} → S₁.wk {n} ⟨ _∼_ ⟩ S₂.wk {n}
    wk = wk⋆ 1

    -- A substitution which only replaces the first variable.
    sub : ∀ {n} {t₁ : T₁ n} {t₂} → t₁ ∼ t₂ → S₁.sub t₁ ⟨ _∼_ ⟩ S₂.sub t₂
    sub t₁~t₂ = t₁~t₂ ∷ id

  -- Application of substitutions lifted to relations.
  record RelApplication {T₁′ T₂′} (R : TermRel T₁′ T₂′)
                        (app₁ : Application T₁ T₁′)
                        (app₂ : Application T₂ T₂′) : Set where
    private
      module A₁ = Application app₁
      module A₂ = Application app₂
    open LiftTermRel T₁′ T₂′ using () renaming (_⟨_⟩_ to _⟨_⟩′_)

    infixl 8 _/_
    infixl 9 _⊙_

    -- Post-application of substitutions to things.
    field _/_ : ∀ {m n t₁ t₂} {σ₁ : Sub T₁′ m n} {σ₂ : Sub T₂′ m n} →
                t₁ ∼ t₂ → σ₁ ⟨ R ⟩′ σ₂ → (t₁ A₁./ σ₁) ∼ (t₂ A₂./ σ₂)

    -- Reverse composition. (Fits well with post-application.)
    _⊙_ : ∀ {m n k} {σ₁ : Sub T₁ m n} {σ₂} {σ₁′ : Sub T₁′ n k} {σ₂′} →
          σ₁ ⟨ _∼_ ⟩ σ₂ → σ₁′ ⟨ R ⟩′ σ₂′ → σ₁ A₁.⊙ σ₁′ ⟨ _∼_ ⟩ σ₂ A₂.⊙ σ₂′
    σ₁∼σ₂ ⊙ σ₁∼σ₂′ = gmap₂ (λ t₁∼t₂ → t₁∼t₂ / σ₁∼σ₂′) σ₁∼σ₂

  -- A combination of the two records above.
  record RelSubst (subst₁ : Subst T₁) (subst₂ : Subst T₂) : Set where
    private
      module S₁ = Subst subst₁
      module S₂ = Subst subst₂

    field
      simple      : RelSimple          S₁.simple      S₂.simple
      application : RelApplication _∼_ S₁.application S₂.application

    open RelSimple      simple      public
    open RelApplication application public

------------------------------------------------------------------------
-- Instantiations and code for facilitating instantiations

-- Liftings from TermRel T₁ T₂ to TermRel T₁′ T₂′.
record RelLift {T₁ T₂ T₁′ T₂′} (_∼_ : TermRel T₁ T₂) (_∼′_ : TermRel T₁′ T₂′)
               (l₁ : Lift T₁ T₁′) (l₂ : Lift T₂ T₂′) : Set where
  private
    module L₁ = Lift l₁
    module L₂ = Lift l₂

  field
    simple : RelSimple _∼_ L₁.simple L₂.simple
    lift   : ∀ {n} {t₁ : T₁ n} {t₂} → t₁ ∼ t₂ → L₁.lift t₁ ∼′ L₂.lift t₂

  open RelSimple simple public

-- Variable substitutions (renamings) lifted to equality.
module VarEqSubst where
  private module V = VarSubst

  infix 4 _⟨≡⟩_

  _⟨≡⟩_ : SubRel Fin Fin
  _⟨≡⟩_ = LiftTermRel.lift Fin Fin _≡_

  subst : RelSubst _≡_ V.subst V.subst
  subst = record
    { simple      = record { extension = extension; var = λ _ → refl }
    ; application = record { _/_ = _/_ }
    }
    where
      extension = record { weaken = cong suc }

      _/_ : ∀ {m n x₁ x₂} {σ₁ σ₂ : Sub Fin n m} →
            x₁ ≡ x₂ → σ₁ ⟨≡⟩ σ₂ → x₁ V./ σ₁ ≡ x₂ V./ σ₂
      _/_ {x₁ = x} refl σ₁≡σ₂ = lookup₂ x σ₁≡σ₂

  open RelSubst subst public

-- "Term" substitutions lifted to relations.
record TermRelSubst {T₁ T₂ : ℕ → Set} (_∼_ : TermRel T₁ T₂)
                    (ts₁ : TermSubst T₁) (ts₂ : TermSubst T₂) : Set₁ where
  private
    module S₁ = TermSubst ts₁
    module S₂ = TermSubst ts₂
    module V  = VarEqSubst

  field
    var : ∀ {n} (x : Fin n) → S₁.var x ∼ S₂.var x
    app : ∀ {T₁′ T₂′} (R : TermRel T₁′ T₂′)
          (l₁ : Lift T₁′ T₁) (l₂ : Lift T₂′ T₂) → RelLift R _∼_ l₁ l₂ →
          let open LiftTermRel T₁′ T₂′ using (_⟨_⟩_) in
          ∀ {m n t₁ t₂} {σ₁ : Sub T₁′ m n} {σ₂ : Sub T₂′ m n} →
          t₁ ∼ t₂ → σ₁ ⟨ R ⟩ σ₂ → S₁.app l₁ t₁ σ₁ ∼ S₂.app l₂ t₂ σ₂

  module RelLifted {T₁′ T₂′} (R : TermRel T₁′ T₂′)
                   (l₁ : Lift T₁′ T₁) (l₂ : Lift T₂′ T₂)
                   (lift : RelLift R _∼_ l₁ l₂) where
    private
      module L₁ = S₁.Lifted l₁
      module L₂ = S₂.Lifted l₂

    application : RelApplication _∼_ R L₁.application L₂.application
    application = record { _/_ = app R l₁ l₂ lift }

  varLift : RelLift _≡_ _∼_ S₁.varLift S₂.varLift
  varLift = record { simple = V.simple; lift = lift }
    where
      lift : ∀ {n} {x₁ x₂ : Fin n} → x₁ ≡ x₂ → S₁.var x₁ ∼ S₂.var x₂
      lift {x₁ = x} refl = var x

  infix 8 _/Var_

  _/Var_ : ∀ {m n t₁ t₂} {σ₁ σ₂ : Sub Fin m n} →
           t₁ ∼ t₂ → σ₁ V.⟨≡⟩ σ₂ → (t₁ S₁./Var σ₁) ∼ (t₂ S₂./Var σ₂)
  _/Var_ = app _≡_ S₁.varLift S₂.varLift varLift

  simple : RelSimple _∼_ S₁.simple S₂.simple
  simple = record
    { extension = record { weaken = λ t₁∼t₂ → t₁∼t₂ /Var V.wk }
    ; var       = var
    }

  termLift : RelLift _∼_ _∼_ S₁.termLift S₂.termLift
  termLift = record { simple = simple; lift = Fun.id }

  subst : RelSubst _∼_ S₁.subst S₂.subst
  subst = record
    { simple      = simple
    ; application = RelLifted.application _∼_ S₁.termLift S₂.termLift termLift
    }

  open LiftTermRel T₁ T₂  public using (_⟨_⟩_)
  open RelSubst subst public hiding (var; simple)
