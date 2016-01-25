------------------------------------------------------------------------
-- Well-typed substitutions
------------------------------------------------------------------------

module Data.Fin.Substitution.Typed where

import Category.Applicative.Indexed as Applicative
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Vec as Vec using (Vec; []; _∷_; map)
open import Data.Vec.All as All
  using (All; All₂; []; _∷_; map₂; gmap₂; gmap₂₁; gmap₂₂)
open import Data.Vec.Properties using (lookup-morphism)
open import Function as Fun using (_∘_; flip)
open import Relation.Binary.PropositionalEquality as PropEq hiding (trans)
open PropEq.≡-Reasoning


------------------------------------------------------------------------
-- Abstract typing contexts and well-typedness relations

-- Abstract typing contexts over T-types.
--
-- A typing context Ctx T n maps n free variables to T-types
-- containing up to n free variables each.
module Context (T : ℕ → Set) where

  infixr 5 _∷_

  -- Typing contexts.
  data Ctx : ℕ → Set where
    []  :                       Ctx 0
    _∷_ : ∀ {n} → T n → Ctx n → Ctx (1 + n)

  -- Operations on contexts that require weakening of types.
  record WeakenOps : Set where

    -- Weakening of types.
    field weaken : ∀ {n} → T n → T (1 + n)

    -- Convert a context to its vector representation.
    toVec : ∀ {n} → Ctx n → Vec (T n) n
    toVec []      = []
    toVec (a ∷ Γ) = weaken a ∷ map weaken (toVec Γ)

    -- Lookup the type of a variable in a context.
    lookup : ∀ {n} → Fin n → Ctx n → T n
    lookup x = Vec.lookup x ∘ toVec

open Context

-- Abstract typings.
--
-- An abtract typing _⊢_∈_ : Typing Tp₁ Tm Tp₂ is a ternary relation
-- which, in a given Tp₁-context, relates Tm-terms to their Tp₂-types.
Typing : (ℕ → Set) → (ℕ → Set) → (ℕ → Set) → Set₁
Typing Tp₁ Tm Tp₂ = ∀ {n} → Ctx Tp₁ n → Tm n → Tp₂ n → Set

-- Abstract well-formedness.
--
-- An abtract well-formedness relation _⊢_wf : Wf Tp₁ Tp₂ is a binary
-- relation which, in a given Tp₁-context, asserts the well-formedness
-- of Tp₂-types.
Wf : (ℕ → Set) → Set₁
Wf Tp = ∀ {n} → Ctx Tp n → Tp n → Set

-- Well-formed contexts.
--
-- A well-formed typing context (Γ wf) is a context Γ in which every
-- participating T-type is well-formed.
module WellFormedContext {T} (_⊢_wf : Wf T) where
  infix  4 _wf
  infixr 5 _∷_

  -- Typing contexts.
  data _wf : ∀ {n} → Ctx T n → Set where
    []  :                                              [] wf
    _∷_ : ∀ {n a} {Γ : Ctx T n} → Γ ⊢ a wf → Γ wf → a ∷ Γ wf

  -- Inversions.

  wf-∷₁ : ∀ {n} {Γ : Ctx T n} {a} → a ∷ Γ wf → Γ ⊢ a wf
  wf-∷₁ (a-wf ∷ _) = a-wf

  wf-∷₂ : ∀ {n} {Γ : Ctx T n} {a} → a ∷ Γ wf → Γ wf
  wf-∷₂ (_ ∷ Γ-wf) = Γ-wf

  -- Operations on well-formed contexts that require weakening of
  -- well-formedness judgments.
  record WfWeakenOps (weakenOps : WeakenOps T) : Set₁ where
    private module W = WeakenOps T weakenOps

    field
      -- Weakening of well-formedness judgments.
      weaken : ∀ {n} {Γ : Ctx T n} {a b} → Γ ⊢ a wf → Γ ⊢ b wf →
               (a ∷ Γ) ⊢ W.weaken b wf

    -- Convert a well-formed context to its All representation.
    toAll : ∀ {n} {Γ : Ctx T n} → Γ wf → All (λ a → Γ ⊢ a wf) (W.toVec Γ)
    toAll []         = []
    toAll (a-wf ∷ Γ) = weaken a-wf a-wf ∷ All.gmap (weaken  a-wf) (toAll Γ)

    -- Lookup the type of a variable in a context.
    lookup : ∀ {n} {Γ : Ctx T n} → (x : Fin n) → Γ wf → Γ ⊢ (W.lookup x Γ) wf
    lookup x = All.lookup x ∘ toAll

-- Trivial well-formedness.
--
-- This module provides a trivial well-formedness relation and the
-- corresponding trivially well-formed contexts.  This is useful when
-- implmenting typed substitutions on types that either lack or do not
-- necessitate a notion well-formedness.
module ⊤-WellFormed {T} (weakenOps : WeakenOps T) where

  infix  4 _⊢_wf

  -- Trivial well-formedness.
  _⊢_wf : Wf T
  _ ⊢ _ wf = ⊤

  open WellFormedContext _⊢_wf public

  -- Trivial well-formedness of contexts.
  ctx-wf : ∀ {n} (Γ : Ctx T n) → Γ wf
  ctx-wf []      = []
  ctx-wf (a ∷ Γ) = tt ∷ ctx-wf Γ

  module ⊤-WfWeakenOps  where

    wfWeakenOps : WfWeakenOps weakenOps
    wfWeakenOps = record { weaken = λ _ _ → tt }

    open WfWeakenOps public


------------------------------------------------------------------------
-- Abstract well-typed substitutions (i.e. substitution lemmas)

-- Abstract typed substitutions.
record TypedSub (Tp₁ Tp₂ Tm : ℕ → Set) : Set₁ where

  infix 4 _⊢_∈_ _⊢_wf

  field
    _⊢_∈_ : Typing Tp₂ Tm Tp₁   -- the associated typing
    _⊢_wf : Wf Tp₂              -- Tp₂-well-formedness

    -- Application of Tm-substitutions to (source) Tp₁-types
    application : Application Tp₁ Tm

    -- Operations on the contexts.
    weakenOps : WeakenOps Tp₁

  open Application       application       public using (_/_)
  open WeakenOps         Tp₁ weakenOps            using (toVec)
  open WellFormedContext _⊢_wf             public

  infix  4 _⇒_⊢_
  infixr 4 _,_

  -- Typed substitutions.
  --
  -- A typed substitution Γ ⇒ Δ ⊢ σ is a substitution σ which, when
  -- applied to something that is well-typed in a source context Γ,
  -- yields something well-typed in a well-formed target context Δ.
  data _⇒_⊢_ {m n} (Γ : Ctx Tp₁ m) (Δ : Ctx Tp₂ n) : Sub Tm m n → Set where
    _,_ : ∀ {σ} → All₂ (λ t a → Δ ⊢ t ∈ (a / σ)) σ (toVec Γ) → Δ wf → Γ ⇒ Δ ⊢ σ

  -- Project out the first component of a typed substitution.
  proj₁ : ∀ {m n} {Γ : Ctx Tp₁ m} {Δ : Ctx Tp₂ n} {σ : Sub Tm m n} →
          Γ ⇒ Δ ⊢ σ → All₂ (λ t a → Δ ⊢ t ∈ (a / σ)) σ (toVec Γ)
  proj₁ (σ-wt , _) = σ-wt

-- Abstract extensions of substitutions.
record ExtensionTyped {Tp₁ Tp₂ Tm} (extension : Extension Tm)
                      (typedSub : TypedSub Tp₁ Tp₂ Tm) : Set where

  open TypedSub typedSub
  private
    module E  = Extension extension
    module C  = WeakenOps Tp₁ weakenOps

  field

    -- Weakens well-typed Tm-terms.
    weaken : ∀ {n} {Δ : Ctx Tp₂ n} {t a b} → Δ ⊢ a wf → Δ ⊢ t ∈ b →
             a ∷ Δ ⊢ E.weaken t ∈ C.weaken b

    -- Weakening commutes with other substitutions.
    weaken-/ : ∀ {m n} {σ : Sub Tm m n} {t} a →
               C.weaken (a / σ) ≡ C.weaken a / (t E./∷ σ)

    -- Well-typedness implies well-formedness of contexts.
    wt-wf : ∀ {n} {Γ : Ctx Tp₂ n} {t a} → Γ ⊢ t ∈ a → Γ wf

  infixr 5 _/∷_

  -- Extension by a typed term.
  _/∷_ : ∀ {m n} {Γ : Ctx Tp₁ m} {Δ : Ctx Tp₂ n} {t a b σ} →
         b ∷ Δ ⊢ t ∈ C.weaken (a / σ) → Γ ⇒ Δ ⊢ σ →
         a ∷ Γ ⇒ b ∷ Δ ⊢ (t E./∷ σ)
  t∈a/σ /∷ (σ-wt , _) = σ-wt′ , wt-wf t∈a/σ
    where
      b∷Δ-wf = wt-wf t∈a/σ
      b-wf   = wf-∷₁ b∷Δ-wf
      t∈a/σ′ = subst (_⊢_∈_ _ _) (weaken-/ _) t∈a/σ
      σ-wt′  =
        t∈a/σ′ ∷ gmap₂ (subst (_⊢_∈_ _ _) (weaken-/ _) ∘ weaken b-wf) σ-wt

-- Abstract simple typed substitutions.
record SimpleTyped {Tp Tm} (simple : Simple Tm)
                   (typedSub : TypedSub Tp Tp Tm) : Set where

  open TypedSub typedSub
  private
    module S  = SimpleExt simple
    module L₀ = Lemmas₀   (record { simple = simple })
    module C  = WeakenOps Tp weakenOps

  field
    extensionTyped : ExtensionTyped (record { weaken = S.weaken }) typedSub

    -- Takes variables to well-typed Tms.
    var : ∀ {n} {Γ : Ctx Tp n} (x : Fin n) → Γ wf → Γ ⊢ S.var x ∈ C.lookup x Γ

    -- Types are invariant under the identity substitution.
    id-vanishes : ∀ {n} (a : Tp n) → a / S.id ≡ a

    -- Relates weakening of types to weakening of Tms.
    /-wk : ∀ {n} {a : Tp n} → a / S.wk ≡ C.weaken a

    -- Single-variable substitution is a left-inverse of weakening.
    wk-sub-vanishes : ∀ {n b} (a : Tp n) → a / S.wk / S.sub b ≡ a

    -- Well-formedness of types implies well-formedness of contexts.
    wf-wf : ∀ {n} {Γ : Ctx Tp n} {a} → Γ ⊢ a wf → Γ wf

  open ExtensionTyped extensionTyped public

  infixl 10 _↑_

  -- Lifting.
  _↑_ : ∀ {m n} {Γ : Ctx Tp m} {Δ : Ctx Tp n} {σ} → Γ ⇒ Δ ⊢ σ →
        ∀ {a} → Δ ⊢ a / σ wf → a ∷ Γ ⇒ a / σ ∷ Δ ⊢ σ S.↑
  (σ-wt , Δ-wf) ↑ a/σ-wf = var zero (a/σ-wf ∷ Δ-wf ) /∷ (σ-wt , Δ-wf)

  -- The identity substitution.
  id : ∀ {n} {Γ : Ctx Tp n} → Γ wf → Γ ⇒ Γ ⊢ S.id
  id             []            = [] , []
  id {Γ = a ∷ Γ} (a-wf ∷ Γ-wf) =
    subst₂ (λ Δ σ → a ∷ Γ ⇒ Δ ⊢ σ)
           (cong (flip _∷_ Γ) (id-vanishes a)) (L₀.id-↑⋆ 1)
           (id Γ-wf ↑ subst (_⊢_wf Γ) (sym (id-vanishes a)) a-wf)

  -- The first component of the identity substitution.
  private
    id₁ : ∀ {n} {Γ : Ctx Tp n} → Γ wf →
          All₂ (λ t a → Γ ⊢ t ∈ (a / S.id)) S.id (C.toVec Γ)
    id₁ = proj₁ ∘ id

  -- Weakening.
  wk : ∀ {n} {Γ : Ctx Tp n} {a} → Γ ⊢ a wf → Γ ⇒ a ∷ Γ ⊢ S.wk
  wk a-wf =
    gmap₂₁ (weaken′ a-wf ∘ subst (_⊢_∈_ _ _) (id-vanishes _)) (id₁ Γ-wf) ,
      a-wf ∷ Γ-wf
    where
      weaken′ : ∀ {n} {Γ : Ctx Tp n} {t a b} → Γ ⊢ a wf → Γ ⊢ t ∈ b →
                a ∷ Γ ⊢ S.weaken t ∈ b / S.wk
      weaken′ a-wf = subst (_⊢_∈_ _ _) (sym /-wk) ∘ weaken a-wf

      Γ-wf = wf-wf a-wf

  -- Some helper lemmas.
  private
    wk-sub-vanishes′ : ∀ {n a} {t : Tm n} → a ≡ C.weaken a / S.sub t
    wk-sub-vanishes′ {a = a} {t} = begin
      a                      ≡⟨ sym (wk-sub-vanishes a) ⟩
      a / S.wk / S.sub t     ≡⟨ cong (flip _/_ _) /-wk ⟩
      C.weaken a / S.sub t   ∎

    id-wk-sub-vanishes : ∀ {n a} {t : Tm n} →
                         a / S.id ≡ C.weaken a / S.sub t
    id-wk-sub-vanishes {a = a} {t} = begin
      a / S.id               ≡⟨ id-vanishes a ⟩
      a                      ≡⟨ wk-sub-vanishes′ ⟩
      C.weaken a / S.sub t   ∎

  -- A substitution which only replaces the first variable.
  sub : ∀ {n} {Γ : Ctx Tp n} {t a} → Γ ⊢ t ∈ a → a ∷ Γ ⇒ Γ ⊢ S.sub t
  sub t∈a =
    t∈a′ ∷ gmap₂₂ (subst (_⊢_∈_ _ _) id-wk-sub-vanishes) (id₁ Γ-wf) , Γ-wf
    where
      Γ-wf = wt-wf t∈a
      t∈a′ = subst (_⊢_∈_ _ _) wk-sub-vanishes′ t∈a

  -- A substitution which only changes the type of the first variable.
  tsub : ∀ {n} {Γ : Ctx Tp n} {a b} → b ∷ Γ ⊢ S.var zero ∈ C.weaken a →
         a ∷ Γ ⇒ b ∷ Γ ⊢ S.id
  tsub z∈a = z∈a′ /∷ id (wf-∷₂ (wt-wf z∈a))
    where
      z∈a′ = subst (_⊢_∈_ _ _) (cong C.weaken (sym (id-vanishes _))) z∈a

-- Abstract typed liftings from Tm₁ to Tm₂.
record LiftTyped {Tp Tm₁ Tm₂} (l : Lift Tm₁ Tm₂)
                 (typedSub : TypedSub Tp Tp Tm₁)
                 (_⊢₂_∈_   : Typing Tp Tm₂ Tp)   : Set where

  open TypedSub typedSub renaming (_⊢_∈_ to _⊢₁_∈_)
  private module L = Lift l

  -- The underlying well-typed simple Tm₁-substitutions.
  field simpleTyped : SimpleTyped L.simple typedSub

  open SimpleTyped simpleTyped public

  -- Lifts well-typed Tm₁-terms to well-typed Tm₂-terms.
  field lift : ∀ {n} {Γ : Ctx Tp n} {t a} → Γ ⊢₁ t ∈ a → Γ ⊢₂ (L.lift t) ∈ a

-- Abstract variable typings.
module VarTyping {Tp} (weakenOps : WeakenOps Tp) (_⊢_wf : Wf Tp) where
  open WeakenOps Tp weakenOps
  open WellFormedContext _⊢_wf

  infix 4 _⊢Var_∈_

  -- Abstract variable typings.
  data _⊢Var_∈_ {n} (Γ : Ctx Tp n) : Fin n → Tp n → Set where
    var : ∀ x → Γ wf → Γ ⊢Var x ∈ lookup x Γ

-- Abstract typed variable substitutions (renamings).
record TypedVarSubst {Tp} (_⊢_wf : Wf Tp) : Set where
  field
    application : Application Tp Fin
    weakenOps   : WeakenOps Tp

  open WellFormedContext   _⊢_wf
  open VarTyping weakenOps _⊢_wf public

  typedSub : TypedSub Tp Tp Fin
  typedSub = record
    { _⊢_∈_       = _⊢Var_∈_
    ; _⊢_wf       = _⊢_wf
    ; application = application
    ; weakenOps   = weakenOps
    }

  open TypedSub typedSub public using () renaming (_⇒_⊢_ to _⇒_⊢Var_)

  open Application application       using (_/_)
  open Lemmas₄     VarLemmas.lemmas₄ using (id; wk; _⊙_)
  private module C = WeakenOps Tp weakenOps

  field
    /-wk        : ∀ {n} {a : Tp n} → a / wk ≡ C.weaken a
    id-vanishes : ∀ {n} (a : Tp n) → a / id ≡ a
    /-⊙         : ∀ {m n k} {σ₁ : Sub Fin m n} {σ₂ : Sub Fin n k} a →
                  a / σ₁ ⊙ σ₂ ≡ a / σ₁ / σ₂
    wf-wf       : ∀ {n} {Γ : Ctx Tp n} {a} → Γ ⊢ a wf → Γ wf

  appLemmas : AppLemmas Tp Fin
  appLemmas = record
    { application = application
    ; lemmas₄     = VarLemmas.lemmas₄
    ; id-vanishes = id-vanishes
    ; /-⊙         = /-⊙
    }

  open ExtAppLemmas appLemmas using (wk-commutes; wk-sub-vanishes)
  open SimpleExt VarLemmas.simple using (extension; _/∷_)

  -- Extensions of renamings.
  extensionTyped : ExtensionTyped extension typedSub
  extensionTyped = record
    { weaken          = weaken
    ; weaken-/        = weaken-/
    ; wt-wf           = wt-wf
    }
    where
      open Applicative.Morphism using (op-<$>)

      weaken : ∀ {n} {Γ : Ctx Tp n} {x a b} → Γ ⊢ a wf → Γ ⊢Var x ∈ b →
               a ∷ Γ ⊢Var suc x ∈ C.weaken b
      weaken a-wf (var x Γ-wf) =
        subst (_⊢Var_∈_ _ _) (op-<$> (lookup-morphism x) _ _)
              (var (suc x) (a-wf ∷ Γ-wf))

      weaken-/ : ∀ {m n} {σ : Sub Fin m n} {t} a →
                 C.weaken (a / σ) ≡ C.weaken a / (t /∷ σ)
      weaken-/ {σ = σ} {t} a = begin
        C.weaken (a / σ)        ≡⟨ sym /-wk ⟩
        a / σ / wk              ≡⟨ wk-commutes a ⟩
        a / wk / (t /∷ σ)       ≡⟨ cong₂ _/_ /-wk refl ⟩
        C.weaken a / (t /∷ σ)   ∎

      wt-wf : ∀ {n} {Γ : Ctx Tp n} {x a} → Γ ⊢Var x ∈ a → Γ wf
      wt-wf (var x Γ-wf) = Γ-wf

  -- Simple typed renamings.
  simpleTyped : SimpleTyped VarLemmas.simple typedSub
  simpleTyped = record
    { extensionTyped  = extensionTyped
    ; var             = var
    ; id-vanishes     = id-vanishes
    ; /-wk            = /-wk
    ; wk-sub-vanishes = wk-sub-vanishes
    ; wf-wf           = wf-wf
    }

  open SimpleTyped simpleTyped public
    hiding (extensionTyped; var; /-wk; id-vanishes; wk-sub-vanishes; wf-wf)
