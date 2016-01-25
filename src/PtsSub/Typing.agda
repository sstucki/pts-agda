------------------------------------------------------------------------
-- Typing of pure type systems with subtyping (PTS-≤)
------------------------------------------------------------------------

module PtsSub.Typing where

open import Data.Fin using (Fin; zero)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Fin.Substitution.Typed
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_,_; ∃; _×_; proj₂)
open import Data.Star using (ε; _◅_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec.All using (lookup₂)
open import Function using (flip)
open import Relation.Binary
import Relation.Binary.PropositionalEquality as PropEq

open import PtsSub.Core public
open import PtsSub.Syntax using (module SubstApp)
open import PtsSub.Reduction.Full


------------------------------------------------------------------------
-- Typing derivations.

-- Definitions and lemmas are parametrized by a given PTS instance.
module Typing (pts : PTS-≤) where
  open PTS-≤ pts
  open Ctx
  open Syntax
  open Substitution using (_[_])

  infix  10 _!
  infixl 9  _·_ _…_∈_
  infix  8  ⟨_⟩
  infix  4  _⊢_∈_ _wf

  mutual

    -- Well-formed contexts.
    _wf : ∀ {n} → Ctx n → Set
    Γ wf = WfCtx._wf _⊢_∈_ Γ

    -- Typing derivations.
    data _⊢_∈_ {n} (Γ : Ctx n) : Term n → Term n → Set where
      var    : ∀ x                         → Γ wf → Γ ⊢ var x   ∈ lookup x Γ
      axiom  : ∀ {s₁ s₂} (a : Axiom s₁ s₂) → Γ wf → Γ ⊢ sort s₁ ∈ sort s₂
      Π      : ∀ {s₁ s₂ s₃ a b} (r : Π-Rule s₁ s₂ s₃) →
               Γ ⊢ a ∈ sort s₁  → a ∷ Γ ⊢ b ∈ sort s₂ → Γ ⊢ Π a b ∈ sort s₃
      ƛ      : ∀ {a t b s}      →
               a ∷ Γ ⊢ t ∈ b    → Γ ⊢ Π a b ∈ sort s  → Γ ⊢ ƛ a t ∈ Π a b
      _·_    : ∀ {f a b t}      →
               Γ ⊢ f ∈ Π a b    → Γ ⊢ t ∈ a  → Γ ⊢ f · t ∈ b [ t ]
      _…_∈_  : ∀ {s₁ s₂ a b}    →
               Γ ⊢ a ∈ sort s₁  → Γ ⊢ b ∈ sort s₁ →
               …-Rule s₁ s₂     → a ≡β b → Γ ⊢ (a … b ∈ s₁) ∈ sort s₂
      ⟨_⟩    : ∀ {a b s₁ s₂}    → Γ ⊢ (a … b ∈ s₁) ∈ sort s₂ →
               Γ ⊢ ⟨ a ⟩ ∈ (a … b ∈ s₁)
      _!     : ∀ {t a b s}      → Γ ⊢ t ∈ a … b ∈ s   → Γ ⊢ t ! ∈ sort s
      conv   : ∀ {t a b s}      → Γ ⊢ t ∈ a  →
               Γ ⊢ b ∈ sort s   → a ≡β b     → Γ ⊢ t ∈ b

  open WfCtx _⊢_∈_ public hiding (_wf; _⊢_wf)


------------------------------------------------------------------------
-- Properties of typings

module _ {pts} where
  open PTS-≤  pts
  open Syntax
  open Ctx
  open Typing pts

  -- Contexts of typings are well-formed.
  wt-wf : ∀ {n} {Γ : Ctx n} {t a} → Γ ⊢ t ∈ a → Γ wf
  wt-wf (var x Γ-wf)       = Γ-wf
  wt-wf (axiom a Γ-wf)     = Γ-wf
  wt-wf (Π r a∈s₁ b∈s₂)    = wt-wf a∈s₁
  wt-wf (ƛ t∈b Πab∈s)      = wt-wf Πab∈s
  wt-wf (f∈Πab · t∈a)      = wt-wf f∈Πab
  wt-wf ((a∈s₁ … b∈s₁ ∈ r) a≡b) = wt-wf a∈s₁
  wt-wf ⟨ a…a∈s ⟩          = wt-wf a…a∈s
  wt-wf (t∈a…b !)          = wt-wf t∈a…b
  wt-wf (conv t∈a b∈s a≡b) = wt-wf t∈a

  -- Contexts of well-formed types are well-formed.
  wf-wf : ∀ {n} {Γ : Ctx n} {a} → (∃ λ s → Γ ⊢ a ∈ sort s) → Γ wf
  wf-wf (_ , a∈s) = wt-wf a∈s

  private
    module Sβ {n} where
      open Setoid (≡β-setoid {Sort} {n}) public using (refl; trans; sym)

  -- An inversion lemma for sorts.
  sort-inv : ∀ {n} {Γ : Ctx n} {s a} → Γ ⊢ sort s ∈ a →
             ∃ λ s′ →  Axiom s s′ × a ≡β sort s′
  sort-inv (axiom ax Γ-wf)      = _ , ax , Sβ.refl
  sort-inv (conv s∈a b∈s₁ a≡b) =
    let s₂ , ax , a≡s₂ = sort-inv s∈a
    in s₂ , ax , Sβ.trans (Sβ.sym a≡b) a≡s₂

  -- An inversion lemma for product typings.
  Π-inv : ∀ {n} {Γ : Ctx n} {a b c} → Γ ⊢ Π a b ∈ c →
          ∃ λ s₁ → ∃ λ s₂ → ∃ λ s₃ → Π-Rule s₁ s₂ s₃ ×
            Γ ⊢ a ∈ sort s₁ × a ∷ Γ ⊢ b ∈ sort s₂ × c ≡β sort s₃
  Π-inv (Π r a∈s₁ b∈s₂)          = _ , _ , _ , r , a∈s₁ , b∈s₂ , Sβ.refl
  Π-inv (conv Πab∈c₁ c₂∈s c₁≡c₂) =
    let s₁ , s₂ , s₃ , r , a∈s₁ , b∈s₂ , c₁≡s₃ = Π-inv Πab∈c₁
    in s₁ , s₂ , s₃ , r , a∈s₁ , b∈s₂ , Sβ.trans (Sβ.sym c₁≡c₂) c₁≡s₃

  -- An inversion lemma for abstractions.
  ƛ-inv : ∀ {n} {Γ : Ctx n} {a t c} → Γ ⊢ ƛ a t ∈ c →
          ∃ λ s → ∃ λ b → Γ ⊢ Π a b ∈ sort s × a ∷ Γ ⊢ t ∈ b × c ≡β Π a b
  ƛ-inv (ƛ t∈b Πab∈s)            = _ , _ , Πab∈s , t∈b , Sβ.refl
  ƛ-inv (conv λat∈c₁ c₂∈s c₁≡c₂) =
    let s , b , Πab∈s , t∈b , c₁≡Πab = ƛ-inv λat∈c₁
    in s , b , Πab∈s , t∈b , Sβ.trans (Sβ.sym c₁≡c₂) c₁≡Πab

  -- An inversion lemma for interval typings.
  …-inv : ∀ {n} {Γ : Ctx n} {a b c s₁} → Γ ⊢ (a … b ∈ s₁) ∈ c →
          ∃ λ s₂ → Γ ⊢ a ∈ sort s₁ × Γ ⊢ b ∈ sort s₁ ×
            …-Rule s₁ s₂ × a ≡β b × c ≡β sort s₂
  …-inv ((a∈s₁ … b∈s₁ ∈ r) a≡b)  = _ , a∈s₁ , b∈s₁ , r , a≡b , Sβ.refl
  …-inv (conv a…b∈c₁ c₂∈s c₁≡c₂) =
    let s₂ , a∈s₁ , b∈s₁ , r , a≡b , c₁≡s₂ = …-inv a…b∈c₁
    in s₂ , a∈s₁ , b∈s₁ , r , a≡b , Sβ.trans (Sβ.sym c₁≡c₂) c₁≡s₂

  -- An inversion lemma for singletons.
  ⟨⟩-inv : ∀ {n} {Γ : Ctx n} {a b} → Γ ⊢ ⟨ a ⟩ ∈ b →
           ∃ λ c → ∃ λ s₁ → ∃ λ s₂ →
             Γ ⊢ (a … c ∈ s₁) ∈ sort s₂ × b ≡β a … c ∈ s₁
  ⟨⟩-inv ⟨ a…b∈s ⟩                =  _ , _ , _ , a…b∈s , Sβ.refl
  ⟨⟩-inv (conv ⟨a⟩∈b₁ b₂∈s b₁≡b₂) =
    let c , s₁ , s₂ , a…c∈s , b₁≡a…c = ⟨⟩-inv ⟨a⟩∈b₁
    in c , s₁ , s₂ , a…c∈s , Sβ.trans (Sβ.sym b₁≡b₂) b₁≡a…c

  -- An inversion lemma for projections.
  !-inv : ∀ {n} {Γ : Ctx n} {t a} → Γ ⊢ t ! ∈ a →
          ∃ λ b → ∃ λ c → ∃ λ s → Γ ⊢ t ∈ (b … c ∈ s) × a ≡β sort s
  !-inv (t∈b…c !)               =  _ , _ , _ , t∈b…c , Sβ.refl
  !-inv (conv t!∈a₁ a₂∈s a₁≡a₂) =
    let b , c , s , t∈b…c , a₁≡s = !-inv t!∈a₁
    in b , c , s , t∈b…c ,  Sβ.trans (Sβ.sym a₁≡a₂) a₁≡s


  ----------------------------------------------------------------------
  -- Well-typed substitutions (i.e. substitution lemmas)

  -- A shorthand for typings of Ts.
  TermTyping : (ℕ → Set) → Set₁
  TermTyping T = Typing Term T Term

  -- Term-typed substitutions.
  module TermTypedSub {T} (l : Lift T Term) (_⊢T_∈_ : TermTyping T) where
    typedSub : TypedSub Term Term T
    typedSub = record
      { _⊢_∈_       = _⊢T_∈_
      ; _⊢_wf       = WfCtx._⊢_wf _⊢_∈_
      ; application = record { _/_    = SubstApp._/_ Sort l }
      ; weakenOps   = record { weaken = Substitution.weaken }
      }

    open TypedSub typedSub public hiding (_⊢_∈_)

  -- Typed liftings from Ts to Terms.
  LiftToTermTyped : ∀ {T} → Lift T Term → TermTyping T → Set
  LiftToTermTyped l _⊢T_∈_ = LiftTyped l typedSub _⊢_∈_
    where open TermTypedSub l _⊢T_∈_ using (typedSub)

  -- Application of well-typed substitutions to types, paths and
  -- subtyping derivations.
  record TypedSubstApp {T} l {_⊢T_∈_ : TermTyping T}
                       (lt : LiftToTermTyped l _⊢T_∈_) : Set where
    open LiftTyped lt
    open Substitution using (_[_])
    open PropEq hiding ([_])
    private
      module A = SubstApp Sort l
      module L = Lift l

    -- Substitutions commute.
    field /-sub-↑ : ∀ {m n} a b (σ : Sub T m n) →
                    a [ b ] A./ σ ≡ (a A./ σ L.↑) [ b A./ σ ]

    open BetaSubstApp (record { /-sub-↑ = /-sub-↑ }) hiding (/-sub-↑)
    open TermTypedSub l _⊢T_∈_ hiding (_/_)

    infixl 8 _/_

    -- Substitutions preserve well-typedness of terms.
    _/_ : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {t a σ} →
          Γ ⊢ t ∈ a → Γ ⇒ Δ ⊢ σ → Δ ⊢ t A./ σ ∈ a A./ σ
    var x Γ-wf            / (σ-wt , _) = lift (lookup₂ x σ-wt)
    axiom a Γ-wf          / (_ , Δ-wf) = axiom a Δ-wf
    Π r a∈s₁ b∈s₂         / σ-wt =
      Π r (a∈s₁ / σ-wt) (b∈s₂ / σ-wt ↑ (_ , a∈s₁ / σ-wt))
    ƛ t∈b Πab∈s           / σ-wt =
      let _ , _ , _ , _ , a/σ∈s , _ = Π-inv (Πab∈s / σ-wt) in
      ƛ (t∈b / σ-wt ↑ (_ , a/σ∈s)) (Πab∈s / σ-wt)
    _·_ {b = b} f∈Πab t∈a / σ-wt =
      subst (_⊢_∈_ _ _) (sym (/-sub-↑ b _ _)) ((f∈Πab / σ-wt) · (t∈a / σ-wt))
    _…_∈_ a∈s₁ b∈s₁ r a≡b / σ-wt =
      _…_∈_ (a∈s₁ / σ-wt) (b∈s₁ / σ-wt) r (a≡b /≡β _)
    ⟨ a…a∈s ⟩             / σ-wt = ⟨ a…a∈s / σ-wt ⟩
    t∈a…b !               / σ-wt = (t∈a…b / σ-wt) !
    conv t∈a b∈s a≡b      / σ-wt = conv (t∈a / σ-wt) (b∈s / σ-wt) (a≡b /≡β _)

  -- Typed variable substitutions (α-renamings).
  module TypedRenaming where
    open Substitution
      using (termSubst; varLiftAppLemmas; varLiftSubLemmas)
    open TermSubst     termSubst        using  (varLift)
    open LiftAppLemmas varLiftAppLemmas hiding (lift)

    typedVarSubst : TypedVarSubst (WfCtx._⊢_wf _⊢_∈_)
    typedVarSubst = record
      { application = AppLemmas.application appLemmas
      ; weakenOps   = Ctx.weakenOps
      ; id-vanishes = id-vanishes
      ; /-⊙         = /-⊙
      ; /-wk        = PropEq.refl
      ; wf-wf       = wf-wf
      }
    open TypedVarSubst typedVarSubst public

    -- Liftings from Variables to Paths.
    liftTyped : LiftTyped varLift typedSub _⊢_∈_
    liftTyped = record
      { simpleTyped  = simpleTyped
      ; lift         = lift
      }
      where
        lift : ∀ {n} {Γ : Ctx n} {x a} → Γ ⊢Var x ∈ a → Γ ⊢ var x ∈ a
        lift (var x Γ-wf) = var x Γ-wf

    open LiftSubLemmas varLiftSubLemmas

    typedSubstApp : TypedSubstApp varLift liftTyped
    typedSubstApp = record { /-sub-↑ = /-sub-↑ }

  -- Typed term substitutions in terms.
  module TypedSubstitution where
    open Substitution using (simple; termSubst)
    open TermSubst termSubst using (termLift)
    open TermTypedSub termLift _⊢_∈_ public using (typedSub; _⇒_⊢_)
    open TypedRenaming using (_⇒_⊢α_)
    private
      module U = Substitution
      module V = TypedRenaming
      module L = ExtAppLemmas U.appLemmas

    infixl 8 _/α_ _/_

    -- Renaming preserves well-typedness.
    _/α_ : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a b σ} →
           Γ ⊢ a ∈ b → Γ ⇒ Δ ⊢α σ → Δ ⊢ a U./α σ ∈ b U./α σ
    _/α_ = TypedSubstApp._/_ V.typedSubstApp

    -- Weakening preserves well-typedness.
    weaken : ∀ {n} {Γ : Ctx n} {a b c s} → Γ ⊢ a ∈ b → Γ ⊢ c ∈ sort s →
             (c ∷ Γ) ⊢ (U.weaken a) ∈ (U.weaken b)
    weaken a∈b c∈s = a∈b /α V.wk (_ , c∈s)

    -- A variant of weakening tailored to _°∷_.
    weaken° : ∀ {n} {Γ : Ctx n} {a b c s} → Γ ⊢ a ∈ b → c °∷ Γ ⊢ c ∈ sort s →
             (c °∷ Γ) ⊢ (U.weaken a) ∈ (U.weaken b)
    weaken° a∈b c∈s = a∈b /α V.wk° (_ , c∈s)

    -- Extensions of path substitutions.
    extensionTyped : ExtensionTyped simple typedSub
    extensionTyped = record
      { weaken          = λ { (_ , c∈s) a∈b → weaken a∈b c∈s }
      ; weaken°         = λ { (_ , c∈s) a∈b → weaken° a∈b c∈s }
      ; wk-commutes     = L.wk-commutes
      ; /-wk            = λ {_ a} → L./-wk {t = a}
      ; wt-wf           = wt-wf
      }

    -- Simple typed path substitutions.
    simpleTyped : SimpleTyped simple typedSub
    simpleTyped = record
      { extensionTyped  = extensionTyped
      ; var             = var
      ; id-vanishes     = L.id-vanishes
      ; wk-sub-vanishes = L.wk-sub-vanishes
      ; wf-wf           = wf-wf
      }

    -- Liftings from Variables to Paths.
    liftTyped : LiftTyped termLift typedSub _⊢_∈_
    liftTyped = record
      { simpleTyped  = simpleTyped
      ; lift         = Function.id
      }

    open LiftTyped liftTyped public
      hiding (var; weaken; weaken°; extensionTyped; simpleTyped; wt-wf; wf-wf)

    typedSubstApp : TypedSubstApp termLift liftTyped
    typedSubstApp = record { /-sub-↑ = λ a _ _ → L.sub-commutes a }

    -- Substitutions preserve well-typedness.
    _/_ : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a b σ} →
          Γ ⊢ a ∈ b → Γ ⇒ Δ ⊢ σ → Δ ⊢ a U./ σ ∈ b U./ σ
    _/_ = TypedSubstApp._/_ typedSubstApp

    infix 10 _[_]

    -- Single-variable substitutions preserve well-typedness.
    _[_] : ∀ {n} {Γ : Ctx n} {t a u b} →
           b ∷ Γ ⊢ t ∈ a → Γ ⊢ u ∈ b → Γ ⊢ t U.[ u ] ∈ a U.[ u ]
    t∈a [ u∈b ] = t∈a / sub u∈b

    -- Conversion of the first type in a context preserves
    -- well-typedness.
    conv-⊢ : ∀ {n} {Γ : Ctx n} {a₁ a₂ t b s} →
             a₁ ∷ Γ ⊢ t ∈ b → Γ ⊢ a₂ ∈ sort s → a₁ ≡β a₂ → a₂ ∷ Γ ⊢ t ∈ b
    conv-⊢ t∈b a₂∈s a₁≡a₂ =
      subst₂ (_⊢_∈_ _) (L.id-vanishes _) (L.id-vanishes _) (t∈b / csub)
      where
        open PropEq using (subst₂)
        open BetaSubstitution using (weaken-≡β)
        open Setoid ≡β-setoid using (sym)

        a₁∷Γ-wf = wt-wf t∈b
        a₁∈s′   = proj₂ (wf-∷₁ a₁∷Γ-wf)
        a₂∷Γ-wf = (_ , a₂∈s) ∷ (wf-∷₂ a₁∷Γ-wf)

        csub = tsub (conv (var zero a₂∷Γ-wf) (weaken a₁∈s′ a₂∈s)
                          (weaken-≡β (sym a₁≡a₂)))

  open TypedSubstitution

  -- Operations on well-formed contexts that require weakening of
  -- well-formedness judgments.
  module WfCtxOps where
    private module E = ExtensionTyped extensionTyped

    wfWeakenOps : WfWeakenOps weakenOps
    wfWeakenOps = record
      { weaken  = λ { a-wk (_ , b∈s) → (_ , E.weaken  a-wk b∈s) }
      ; weaken° = λ { a-wk (_ , b∈s) → (_ , E.weaken° a-wk b∈s) }
      }

    open WfWeakenOps wfWeakenOps public


  ----------------------------------------------------------------------
  -- Preservation of types under reduction (aka subject reduction)

  open Sβ
  open PropEq using (_≡_)

  -- Every well-typed term is either a type or an element.
  tp-or-el : ∀ {n} {Γ : Ctx n} {a b} → Γ ⊢ a ∈ b →
             ∃ λ s → b ≡ sort s ⊎ Γ ⊢ b ∈ sort s
  tp-or-el (var x Γ-wf)    = _ , inj₂ (proj₂ (WfCtxOps.lookup x Γ-wf))
  tp-or-el (axiom a Γ-wf)  = _ , inj₁ PropEq.refl
  tp-or-el (Π r a∈s₁ b∈s₂) = _ , inj₁ PropEq.refl
  tp-or-el (ƛ t∈b Πab∈s)   = _ , inj₂ Πab∈s
  tp-or-el (f∈Πab · t∈a)   with tp-or-el f∈Πab
  tp-or-el (f∈Πab · t∈a)   | _ , inj₁ ()
  tp-or-el (f∈Πab · t∈a)   | _ , inj₂ Πab∈s =
    let _ , s , _ , _ , _ , b∈s , _ = Π-inv Πab∈s
    in s , inj₂ (b∈s [ t∈a ])
  tp-or-el ((a∈s₁ … b∈s₂ ∈ r) a≡b) = _ , inj₁ PropEq.refl
  tp-or-el ⟨ a…a∈s ⟩               = _ , inj₂ a…a∈s
  tp-or-el (t∈a…b !)               = _ , inj₁ PropEq.refl
  tp-or-el (conv t∈a b∈s a≡b)      = _ , inj₂ b∈s

  -- An inversion lemma for product typings.
  Π-inv₂ : ∀ {n} {Γ : Ctx n} {f a b} → Γ ⊢ f ∈ Π a b →
           ∃ λ s₁ → ∃ λ s₂ → Γ ⊢ a ∈ sort s₁ × a ∷ Γ ⊢ b ∈ sort s₂
  Π-inv₂ f∈Πab with tp-or-el f∈Πab
  Π-inv₂ f∈Πab | _ , inj₁ ()
  Π-inv₂ f∈Πab | _ , inj₂ Πab∈s =
    let s₁ , s₂ , _ , _ , a∈s₁ , b∈s₂ , _ = Π-inv Πab∈s
    in s₁ , s₂ , a∈s₁ , b∈s₂

  -- A more precise inversion lemma for abstractions.
  ƛ-inv₂ : ∀ {n} {Γ : Ctx n} {a t b c} → Γ ⊢ ƛ a t ∈ Π b c →
           ∃ λ s → Γ ⊢ a ∈ sort s × b ≡β a × a ∷ Γ ⊢ t ∈ c
  ƛ-inv₂ λat∈Πbc =
    let _ , _ , Πad∈s , t∈d , Πbc≡Πad = ƛ-inv  λat∈Πbc
        s₁ , _ , _ , _ , a∈s₁ , _     = Π-inv  Πad∈s
        _ , _ , _ , c∈s₂              = Π-inv₂ λat∈Πbc
        b≡a , c≡d                     = Π-inj  Πbc≡Πad
    in s₁ , a∈s₁ , b≡a , conv t∈d (conv-⊢ c∈s₂ a∈s₁ b≡a) (sym c≡d)

  -- A more precise inversion lemma for singletons.
  ⟨⟩-inv₂ : ∀ {n} {Γ : Ctx n} {a b c s} → Γ ⊢ ⟨ a ⟩ ∈ b … c ∈ s →
            Γ ⊢ a ∈ sort s × b ≡β a
  ⟨⟩-inv₂ ⟨a⟩∈b…c =
    let _ , _ , _ , a…d∈s₂ , b…c≡a…d = ⟨⟩-inv ⟨a⟩∈b…c
        _ , a∈s₁ , _ , _ , _ , _     = …-inv  a…d∈s₂
        b≡a , c≡d , s≡s₁             = …-inj b…c≡a…d
    in PropEq.subst (λ s → _⊢_∈_ _ _ (sort s)) (PropEq.sym s≡s₁) a∈s₁ , b≡a


  -- Preservation of types under one-step reduction.
  pres : ∀ {n} {Γ : Ctx n} {a a′ b} → Γ ⊢ a ∈ b → a →β a′ → Γ ⊢ a′ ∈ b
  pres (var _ _)   ()
  pres (axiom _ _) ()
  pres (Π r a∈s₁ b∈s₂) (Π₁ a→a′ b) =
    Π r a′∈s₂ (conv-⊢ b∈s₂ a′∈s₂ (→β⇒≡β a→a′))
    where a′∈s₂ = pres a∈s₁ a→a′
  pres (Π r a∈s₁ b∈s₂) (Π₂ a b→b′) = Π r a∈s₁ (pres b∈s₂ b→b′)
  pres (ƛ t∈b Πab∈s) (ƛ₁ a→a′ t)   =
    let _ , _ , _ , _ , a′∈s , _ = Π-inv (pres Πab∈s (Π₁ a→a′ _))
        Πab→Πa′b                 = Π₁ a→a′ _
    in conv (ƛ (conv-⊢ t∈b a′∈s (→β⇒≡β a→a′)) (pres Πab∈s Πab→Πa′b))
            Πab∈s (sym (→β⇒≡β Πab→Πa′b))
  pres (ƛ t∈b Πab∈s) (ƛ₂ a t→t′)    = ƛ (pres t∈b t→t′) Πab∈s
  pres (λat∈Πbc · u∈b) (ƛ· a t u) =
    let _ , a∈s , b≡a , t∈c = ƛ-inv₂ λat∈Πbc
    in t∈c [ conv u∈b a∈s b≡a ]
  pres (f∈Πab · t∈a) (f→f′ ·₁ t) = pres f∈Πab f→f′ · t∈a
  pres (_·_ {b = b} f∈Πab t∈a) (f ·₂ t→t′) =
    let _ , _ , _ , b∈s = Π-inv₂ f∈Πab
    in conv (f∈Πab · pres t∈a t→t′) (b∈s [ t∈a ])
            (sym (→β*⇒≡β (b [→β t→t′ ])))
  pres (_…_∈_ a∈s₁ b∈s₁ r a≡b) (a→a′ …₁ b) =
    _…_∈_ (pres a∈s₁ a→a′) b∈s₁ r (trans (sym (→β⇒≡β a→a′)) a≡b)
  pres (_…_∈_ a∈s₁ b∈s₁ r a≡b) (a …₂ b→b′) =
    _…_∈_ a∈s₁ (pres b∈s₁ b→b′) r (trans a≡b (→β⇒≡β b→b′))
  pres ⟨ a…b∈s ⟩ ⟨ a→a′ ⟩ =
    let a…b→a′…b = a→a′ …₁ _
        a′…b∈s   = pres a…b∈s a…b→a′…b
    in conv ⟨ a′…b∈s ⟩ a…b∈s (sym (→β⇒≡β a…b→a′…b))
  pres (t∈a…b !) (t→t′ !)    = (pres t∈a…b t→t′) !
  pres (⟨a₁⟩∈a₂…b !) ⟨ a₁ ⟩! = let a₁∈s , _ = ⟨⟩-inv₂ ⟨a₁⟩∈a₂…b in a₁∈s
  pres (conv a∈b₁ b₂∈s b₁≡b₂) a→a′ = conv (pres a∈b₁ a→a′) b₂∈s b₁≡b₂

  -- Preservation of types under reduction (aka subject reduction).
  pres* : ∀ {n} {Γ : Ctx n} {a a′ b} → Γ ⊢ a ∈ b → a →β* a′ → Γ ⊢ a′ ∈ b
  pres* a∈b  ε                = a∈b
  pres* a₁∈b (a₁→a₂ ◅ a₂→*a₃) = pres* (pres a₁∈b a₁→a₂) a₂→*a₃

