------------------------------------------------------------------------
-- Typing of pure type systems (PTS)
------------------------------------------------------------------------

module Pts.Typing where

open import Data.Fin using (Fin; zero)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Fin.Substitution.Typed
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_,_; ∃; _×_; proj₂)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (flip)
open import Relation.Binary
open import Data.Vec.Relation.Binary.Pointwise.Inductive using () renaming (lookup to lookup₂)
import Relation.Binary.PropositionalEquality as PropEq

open import Pts.Core public
open import Pts.Syntax using (module SubstApp)
open import Pts.Reduction.Full


------------------------------------------------------------------------
-- Typing derivations.
--
-- The presentation of the typing rules below follows that of Pollak
-- (1994) rather than that of Barendregt (1992) in that it uses a
-- separate well-formedness judgment "Γ wf" for contexts in favor of
-- an explicit weakening rule.  The well-formedness judgment is used
-- to strengthen the variable and sort typing rules.  For the
-- remaining rules, well-formedness of contexts is an invariant (as e
-- witnessed by the "wt-wf" Lemma below).
--
-- References:
--
--  * H. P. Barendregt, Lambda Calculi with Types, chapter 2 of the
--    Handbook of Logic in Computer Science (vol. 2), Oxford
--    University Press, 1992.
--
--  * R. Pollack, The Theory of LEGO: A Proof Checker for the Extended
--    Calculus of Constructions, Ph.D. thesis, University of
--    Edinburgh, 1994

-- Definitions and lemmas are parametrized by a given PTS instance.
module Typing (pts : PTS) where
  open PTS pts
  open Ctx
  open Syntax
  open Substitution using (_[_])

  infixl 9 _·_
  infix  4 _wf _⊢_∈_

  mutual

    -- Well-formed contexts.
    _wf : ∀ {n} → Ctx n → Set
    Γ wf = WfCtx._wf _⊢_∈_ Γ

    -- Typing derivations.
    data _⊢_∈_ {n} (Γ : Ctx n) : Term n → Term n → Set where
      var    : ∀ x                         → Γ wf → Γ ⊢ var x   ∈ lookup x Γ
      axiom  : ∀ {s₁ s₂} (a : Axiom s₁ s₂) → Γ wf → Γ ⊢ sort s₁ ∈ sort s₂
      Π      : ∀ {s₁ s₂ s₃ a b} (r : Rule s₁ s₂ s₃)  →
               Γ ⊢ a ∈ sort s₁  → a ∷ Γ ⊢ b ∈ sort s₂ → Γ ⊢ Π a b ∈ sort s₃
      ƛ      : ∀ {a t b s}      →
               a ∷ Γ ⊢ t ∈ b    → Γ ⊢ Π a b ∈ sort s  → Γ ⊢ ƛ a t ∈ Π a b
      _·_    : ∀ {f a b t}      →
               Γ ⊢ f ∈ Π a b    → Γ ⊢ t ∈ a  → Γ ⊢ f · t ∈ b [ t ]
      conv   : ∀ {t a b s}      → Γ ⊢ t ∈ a  →
               Γ ⊢ b ∈ sort s   → a ≡β b     → Γ ⊢ t ∈ b

  open WfCtx _⊢_∈_ public hiding (_wf; _⊢_wf)


------------------------------------------------------------------------
-- Properties of typings

module _ {pts} where
  open PTS    pts
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
  wt-wf (conv t∈a b∈s a≡b) = wt-wf t∈a

  -- Contexts of well-formed types are well-formed.
  wf-wf : ∀ {n} {Γ : Ctx n} {a} → (∃ λ s → Γ ⊢ a ∈ sort s) → Γ wf
  wf-wf (_ , a∈s) = wt-wf a∈s

  private
    module Sβ {n} where
      open Setoid (≡β-setoid {Sort} {n}) public using (refl; trans; sym)

  -- A generation lemma for sorts.
  sort-gen : ∀ {n} {Γ : Ctx n} {s a} → Γ ⊢ sort s ∈ a →
             ∃ λ s′ →  Axiom s s′ × a ≡β sort s′
  sort-gen (axiom ax Γ-wf)      = _ , ax , Sβ.refl
  sort-gen (conv s∈a b∈s₁ a≡b) =
    let s₂ , ax , a≡s₂ = sort-gen s∈a
    in s₂ , ax , Sβ.trans (Sβ.sym a≡b) a≡s₂

  -- A generation lemma for product typings.
  Π-gen : ∀ {n} {Γ : Ctx n} {a b c} → Γ ⊢ Π a b ∈ c →
          ∃ λ s₁ → ∃ λ s₂ → ∃ λ s₃ → Rule s₁ s₂ s₃ ×
            Γ ⊢ a ∈ sort s₁ × a ∷ Γ ⊢ b ∈ sort s₂ × c ≡β sort s₃
  Π-gen (Π r a∈s₁ b∈s₂)          = _ , _ , _ , r , a∈s₁ , b∈s₂ , Sβ.refl
  Π-gen (conv Πab∈c₁ c₂∈s c₁≡c₂) =
    let s₁ , s₂ , s₃ , r , a∈s₁ , b∈s₂ , c₁≡s₃ = Π-gen Πab∈c₁
    in s₁ , s₂ , s₃ , r , a∈s₁ , b∈s₂ , Sβ.trans (Sβ.sym c₁≡c₂) c₁≡s₃

  -- A generation lemma for abstractions.
  ƛ-gen : ∀ {n} {Γ : Ctx n} {a t c} → Γ ⊢ ƛ a t ∈ c →
          ∃ λ s → ∃ λ b → Γ ⊢ Π a b ∈ sort s × a ∷ Γ ⊢ t ∈ b × c ≡β Π a b
  ƛ-gen (ƛ t∈b Πab∈s)            = _ , _ , Πab∈s , t∈b , Sβ.refl
  ƛ-gen (conv λat∈c₁ c₂∈s c₁≡c₂) =
    let s , b , Πab∈s , t∈b , c₁≡Πab = ƛ-gen λat∈c₁
    in s , b , Πab∈s , t∈b , Sβ.trans (Sβ.sym c₁≡c₂) c₁≡Πab


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

  -- Application of well-typed substitutions to terms.
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
    var x Γ-wf            / (σ-wt , _) = lift (lookup₂ σ-wt x)
    axiom a Γ-wf          / (_ , Δ-wf) = axiom a Δ-wf
    Π r a∈s₁ b∈s₂         / σ-wt =
      Π r (a∈s₁ / σ-wt) (b∈s₂ / σ-wt ↑ (_ , a∈s₁ / σ-wt))
    ƛ t∈b Πab∈s           / σ-wt =
      let _ , _ , _ , _ , a/σ∈s , _ = Π-gen (Πab∈s / σ-wt) in
      ƛ (t∈b / σ-wt ↑ (_ , a/σ∈s)) (Πab∈s / σ-wt)
    _·_ {b = b} f∈Πab t∈a / σ-wt =
      subst (_⊢_∈_ _ _) (sym (/-sub-↑ b _ _)) ((f∈Πab / σ-wt) · (t∈a / σ-wt))
    conv t∈a b∈s a≡b      / σ-wt = conv (t∈a / σ-wt) (b∈s / σ-wt) (a≡b /≡β _)

  -- Typed variable substitutions (renamings).
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

    -- Liftings from variables to typed terms.
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
    open SimpleExt simple using (extension)
    open TermSubst termSubst using (termLift)
    open TermTypedSub termLift _⊢_∈_ public using (typedSub; _⇒_⊢_)
    open TypedRenaming using (_⇒_⊢Var_)
    private
      module U = Substitution
      module V = TypedRenaming
      module L = ExtAppLemmas U.appLemmas

    infixl 8 _/Var_ _/_

    -- Renaming preserves well-typedness.
    _/Var_ : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a b σ} →
             Γ ⊢ a ∈ b → Γ ⇒ Δ ⊢Var σ → Δ ⊢ a U./Var σ ∈ b U./Var σ
    _/Var_ = TypedSubstApp._/_ V.typedSubstApp

    -- Weakening preserves well-typedness.
    weaken : ∀ {n} {Γ : Ctx n} {a b c s} → Γ ⊢ a ∈ b → Γ ⊢ c ∈ sort s →
             (c ∷ Γ) ⊢ (U.weaken a) ∈ (U.weaken b)
    weaken a∈b c∈s = a∈b /Var V.wk (_ , c∈s)

    -- Extensions of typed term substitutions.
    extensionTyped : ExtensionTyped extension typedSub
    extensionTyped = record
      { weaken   = λ { (_ , c∈s) a∈b → weaken a∈b c∈s }
      ; weaken-/ = ExtLemmas₄.weaken-/ L.lemmas₄
      ; wt-wf    = wt-wf
      }

    -- Simple typed term substitutions.
    simpleTyped : SimpleTyped simple typedSub
    simpleTyped = record
      { extensionTyped  = extensionTyped
      ; var             = var
      ; id-vanishes     = L.id-vanishes
      ; /-wk            = λ {_ a} → L./-wk {t = a}
      ; wk-sub-vanishes = L.wk-sub-vanishes
      ; wf-wf           = wf-wf
      }

    -- Liftings from terms to terms.
    liftTyped : LiftTyped termLift typedSub _⊢_∈_
    liftTyped = record
      { simpleTyped  = simpleTyped
      ; lift         = Function.id
      }

    open LiftTyped liftTyped public
      hiding (var; weaken; extensionTyped; simpleTyped; wt-wf; wf-wf)

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
      { weaken = λ { a-wk (_ , b∈s) → (_ , E.weaken a-wk b∈s) }
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
    let _ , s , _ , _ , _ , b∈s , _ = Π-gen Πab∈s
    in s , inj₂ (b∈s [ t∈a ])
  tp-or-el (conv t∈a b∈s a≡b) = _ , inj₂ b∈s

  -- An inversion lemma for product typings.
  Π-inv : ∀ {n} {Γ : Ctx n} {f a b} → Γ ⊢ f ∈ Π a b →
           ∃ λ s₁ → ∃ λ s₂ → Γ ⊢ a ∈ sort s₁ × a ∷ Γ ⊢ b ∈ sort s₂
  Π-inv f∈Πab with tp-or-el f∈Πab
  Π-inv f∈Πab | _ , inj₁ ()
  Π-inv f∈Πab | _ , inj₂ Πab∈s =
    let s₁ , s₂ , _ , _ , a∈s₁ , b∈s₂ , _ = Π-gen Πab∈s
    in s₁ , s₂ , a∈s₁ , b∈s₂

  -- An inversion lemma for abstractions.
  ƛ-inv : ∀ {n} {Γ : Ctx n} {a t b c} → Γ ⊢ ƛ a t ∈ Π b c →
           ∃ λ s → Γ ⊢ a ∈ sort s × b ≡β a × a ∷ Γ ⊢ t ∈ c
  ƛ-inv λat∈Πbc =
    let _ , _ , Πad∈s , t∈d , Πbc≡Πad = ƛ-gen λat∈Πbc
        s₁ , _ , _ , _ , a∈s₁ , _     = Π-gen Πad∈s
        _ , _ , _ , c∈s₂              = Π-inv λat∈Πbc
        b≡a , c≡d                     = Π-inj Πbc≡Πad
    in s₁ , a∈s₁ , b≡a , conv t∈d (conv-⊢ c∈s₂ a∈s₁ b≡a) (sym c≡d)

  -- Preservation of types under one-step reduction.
  pres : ∀ {n} {Γ : Ctx n} {a a′ b} → Γ ⊢ a ∈ b → a →β a′ → Γ ⊢ a′ ∈ b
  pres (var _ _)   ()
  pres (axiom _ _) ()
  pres (Π r a∈s₁ b∈s₂) (Π₁ a→a′ b) =
    Π r a′∈s₂ (conv-⊢ b∈s₂ a′∈s₂ (→β⇒≡β a→a′))
    where a′∈s₂ = pres a∈s₁ a→a′
  pres (Π r a∈s₁ b∈s₂) (Π₂ a b→b′) = Π r a∈s₁ (pres b∈s₂ b→b′)
  pres (ƛ t∈b Πab∈s) (ƛ₁ a→a′ t)   =
    let _ , _ , _ , _ , a′∈s , _ = Π-gen (pres Πab∈s (Π₁ a→a′ _))
        Πab→Πa′b                 = Π₁ a→a′ _
    in conv (ƛ (conv-⊢ t∈b a′∈s (→β⇒≡β a→a′)) (pres Πab∈s Πab→Πa′b))
            Πab∈s (sym (→β⇒≡β Πab→Πa′b))
  pres (ƛ t∈b Πab∈s) (ƛ₂ a t→t′)    = ƛ (pres t∈b t→t′) Πab∈s
  pres (λat∈Πbc · u∈b) (cont a t u) =
    let _ , a∈s , b≡a , t∈c = ƛ-inv λat∈Πbc
    in t∈c [ conv u∈b a∈s b≡a ]
  pres (f∈Πab · t∈a) (f→f′ ·₁ t) = pres f∈Πab f→f′ · t∈a
  pres (_·_ {b = b} f∈Πab t∈a) (f ·₂ t→t′) =
    let _ , _ , _ , b∈s = Π-inv f∈Πab
    in conv (f∈Πab · pres t∈a t→t′) (b∈s [ t∈a ])
            (sym (→β*⇒≡β (b [→β t→t′ ])))
  pres (conv a∈b₁ b₂∈s b₁≡b₂) a→a′ = conv (pres a∈b₁ a→a′) b₂∈s b₁≡b₂

  -- Preservation of types under reduction (aka subject reduction).
  pres* : ∀ {n} {Γ : Ctx n} {a a′ b} → Γ ⊢ a ∈ b → a →β* a′ → Γ ⊢ a′ ∈ b
  pres* a∈b  ε                = a∈b
  pres* a₁∈b (a₁→a₂ ◅ a₂→*a₃) = pres* (pres a₁∈b a₁→a₂) a₂→*a₃
