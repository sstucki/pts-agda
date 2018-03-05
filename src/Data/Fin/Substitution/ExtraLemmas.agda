------------------------------------------------------------------------
-- Extra lemmas about substitutions
------------------------------------------------------------------------

module Data.Fin.Substitution.ExtraLemmas where

open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Star using (Star; ε; _◅_; _▻_)
open import Data.Vec using (Vec; _∷_; lookup; map)
open import Data.Vec.All hiding (lookup; map)
open import Data.Vec.Properties using (lookup-map; map-cong; map-∘)
open import Function using (_∘_; _$_; flip)
open import Relation.Binary.PropositionalEquality as PropEq hiding (subst)
open PropEq.≡-Reasoning

-- Simple extension of substitutions.
--
-- FIXME: this should go into Data.Fin.Substitution.
record Extension (T : ℕ → Set) : Set where
  infixr 5 _/∷_

  field weaken : ∀ {n} → T n → T (suc n)  -- Weakens Ts.

  -- Extension.
  _/∷_ : ∀ {m n} → T (suc n) → Sub T m n → Sub T (suc m) (suc n)
  t /∷ ρ = t ∷ map weaken ρ

-- Helper module
module SimpleExt {T} (simple : Simple T) where
  open Simple simple public

  extension : Extension T
  extension = record { weaken = weaken }
  open Extension extension public hiding (weaken)

-- An generalized version of Data.Fin.Lemmas.Lemmas₀
--
-- FIXME: this should go into Data.Fin.Substitution.Lemmas.
module ExtLemmas₀ {T} (lemmas₀ : Lemmas₀ T) where

  open Lemmas₀   lemmas₀ public hiding (lookup-map-weaken-↑⋆)
  open SimpleExt simple

  -- A generalized variant of Lemmas₀.lookup-map-weaken-↑⋆.
  lookup-map-weaken-↑⋆ : ∀ {m n} k x {ρ : Sub T m n} {t} →
                         lookup x (map weaken ρ ↑⋆ k) ≡
                         lookup (Fin.lift k suc x) ((t /∷ ρ) ↑⋆ k)
  lookup-map-weaken-↑⋆ zero    x               = refl
  lookup-map-weaken-↑⋆ (suc k) zero            = refl
  lookup-map-weaken-↑⋆ (suc k) (suc x) {ρ} {t} = begin
      lookup x (map weaken (map weaken ρ ↑⋆ k))
    ≡⟨ lookup-map x weaken _ ⟩
      weaken (lookup x (map weaken ρ ↑⋆ k))
    ≡⟨ cong weaken (lookup-map-weaken-↑⋆ k x) ⟩
      weaken (lookup (Fin.lift k suc x) ((t /∷ ρ) ↑⋆ k))
    ≡⟨ sym (lookup-map (Fin.lift k suc x) weaken _) ⟩
      lookup (Fin.lift k suc x) (map weaken ((t /∷ ρ) ↑⋆ k))
    ∎

-- A generalized version of Data.Fin.Lemmas.Lemmas₄
--
-- FIXME: this should go into Data.Fin.Substitution.Lemmas.
module ExtLemmas₄ {T} (lemmas₄ : Lemmas₄ T) where

  open Lemmas₄    lemmas₄ public hiding (⊙-wk; wk-commutes)
  open Lemmas₃    lemmas₃        using (lookup-wk-↑⋆-⊙; /✶-↑✶′)
  open SimpleExt  simple         using (_/∷_)
  open ExtLemmas₀ lemmas₀        using (lookup-map-weaken-↑⋆)

  private

    ⊙-wk′ : ∀ {m n} {ρ : Sub T m n} {t} k →
            ρ ↑⋆ k ⊙ wk ↑⋆ k ≡ wk ↑⋆ k ⊙ (t /∷ ρ) ↑⋆ k
    ⊙-wk′ {ρ = ρ} {t} k = sym (begin
      wk ↑⋆ k ⊙ (t /∷ ρ) ↑⋆ k   ≡⟨ lemma ⟩
      map weaken ρ ↑⋆ k         ≡⟨ cong (λ ρ′ → ρ′ ↑⋆ k) map-weaken ⟩
      (ρ ⊙ wk) ↑⋆ k             ≡⟨ ↑⋆-distrib k ⟩
      ρ ↑⋆ k ⊙ wk ↑⋆ k          ∎)
      where
      lemma = extensionality λ x → begin
          lookup x (wk ↑⋆ k ⊙ (t /∷ ρ) ↑⋆ k)
        ≡⟨ lookup-wk-↑⋆-⊙ k ⟩
          lookup (Fin.lift k suc x) ((t /∷ ρ) ↑⋆ k)
        ≡⟨ sym (lookup-map-weaken-↑⋆ k x) ⟩
          lookup x (map weaken ρ ↑⋆ k)
        ∎

  ⊙-wk : ∀ {m n} {ρ : Sub T m n} {t} → ρ ⊙ wk ≡ wk ⊙ (t /∷ ρ)
  ⊙-wk = ⊙-wk′ zero

  wk-commutes : ∀ {m n} {ρ : Sub T m n} {t′} t →
                t / ρ / wk ≡ t / wk / (t′ /∷ ρ)
  wk-commutes {ρ = ρ} {t} = /✶-↑✶′ (ε ▻ ρ ▻ wk) (ε ▻ wk ▻ (t /∷ ρ)) ⊙-wk′ zero

  -- A handy helper lemma: weakening commutes with substitution.
  weaken-/ : ∀ {m n} {ρ : Sub T m n} {t′} t →
             weaken (t / ρ) ≡ weaken t / (t′ /∷ ρ)
  weaken-/ {ρ = ρ} {t′} t = begin
    weaken (t / ρ)         ≡⟨ sym /-wk ⟩
    t / ρ / wk             ≡⟨ wk-commutes t ⟩
    t / wk / (t′ /∷ ρ)     ≡⟨ cong₂ _/_ /-wk refl ⟩
    weaken t / (t′ /∷ ρ)   ∎

-- A generalize version of Data.Fin.Lemmas.AppLemmas
--
-- FIXME: this should go into Data.Fin.Substitution.Lemmas.
module ExtAppLemmas {T₁ T₂} (appLemmas : AppLemmas T₁ T₂) where

  open AppLemmas appLemmas public hiding (wk-commutes)
  open SimpleExt simple           using (_/∷_)
  private module L₄ = ExtLemmas₄ lemmas₄

  wk-commutes : ∀ {m n} {ρ : Sub T₂ m n} {t′} t →
                t / ρ / wk ≡ t / wk / (t′ /∷ ρ)
  wk-commutes {ρ = ρ} {t} = ⨀→/✶ (ε ▻ ρ ▻ wk) (ε ▻ wk ▻ (t /∷ ρ)) L₄.⊙-wk

-- Lemmas relating T₃ substitutions in T₁ and T₂.
record LiftAppLemmas (T₁ T₂ T₃ : ℕ → Set) : Set where
  field
    lift          : ∀ {n} → T₃ n → T₂ n
    application₁₃ : Application T₁ T₃
    application₂₃ : Application T₂ T₃
    lemmas₂       : Lemmas₄     T₂
    lemmas₃       : Lemmas₄     T₃

  private
    module L₂ = ExtLemmas₄  lemmas₂
    module L₃ = ExtLemmas₄  lemmas₃
    module A₁ = Application application₁₃
    module A₂ = Application application₂₃

  field
    -- Lifting commutes with application of T₃ substitutions.
    lift-/ : ∀ {m n} t {σ : Sub T₃ m n} → lift (t L₃./ σ) ≡ lift t A₂./ σ

    -- Lifting preserves variables.
    lift-var : ∀ {n} (x : Fin n) → lift (L₃.var x) ≡ L₂.var x

    -- Sequences of T₃ substitutions are equivalent when applied to
    -- T₁s if they are equivalent when applied to T₂ variables.
    /✶-↑✶ :
      ∀ {m n} (σs₁ σs₂ : Subs T₃ m n) →
      (∀ k x → L₂.var x A₂./✶ σs₁ L₃.↑✶ k ≡ L₂.var x A₂./✶ σs₂ L₃.↑✶ k) →
       ∀ k t → t        A₁./✶ σs₁ L₃.↑✶ k ≡ t      A₁./✶ σs₂ L₃.↑✶ k

  lift-lookup-⊙ : ∀ {m n k} x {σ₁ : Sub T₃ m n} {σ₂ : Sub T₃ n k} →
                  lift (lookup x (σ₁ L₃.⊙ σ₂)) ≡ lift (lookup x σ₁) A₂./ σ₂
  lift-lookup-⊙ x {σ₁} {σ₂} = begin
    lift (lookup x (σ₁ L₃.⊙ σ₂))   ≡⟨ cong lift (L₃.lookup-⊙ x) ⟩
    lift (lookup x σ₁ L₃./ σ₂)     ≡⟨ lift-/ _ ⟩
    lift (lookup x σ₁) A₂./ σ₂     ∎

  lift-lookup-⨀ : ∀ {m n} x (σs : Subs T₃ m n) →
                  lift (lookup x (L₃.⨀ σs)) ≡ L₂.var x A₂./✶ σs
  lift-lookup-⨀ x ε = begin
    lift (lookup x L₃.id)    ≡⟨ cong lift (L₃.lookup-id x) ⟩
    lift (L₃.var x)          ≡⟨ lift-var x ⟩
    L₂.var x                 ∎
  lift-lookup-⨀ x (σ ◅ ε) = begin
    lift (lookup x σ)        ≡⟨ cong lift (sym L₃.var-/) ⟩
    lift (L₃.var x L₃./ σ)   ≡⟨ lift-/ _ ⟩
    lift (L₃.var x) A₂./ σ   ≡⟨ cong₂ A₂._/_ (lift-var x) refl ⟩
    L₂.var x A₂./ σ          ∎
  lift-lookup-⨀ x (σ ◅ (σ′ ◅ σs′)) = begin
      lift (lookup x (L₃.⨀ σs L₃.⊙ σ))
    ≡⟨ lift-lookup-⊙ x ⟩
      lift (lookup x (L₃.⨀ σs)) A₂./ σ
    ≡⟨ cong₂ A₂._/_ (lift-lookup-⨀ x (σ′ ◅ σs′)) refl ⟩
      L₂.var x A₂./✶ σs A₂./ σ
    ∎
    where σs = σ′ ◅ σs′

  -- Sequences of T₃ substitutions are equivalent when applied to
  -- T₁s if they are equivalent when applied as composites.
  /✶-↑✶′ : ∀ {m n} (σs₁ σs₂ : Subs T₃ m n) →
           (∀ k → L₃.⨀ (σs₁ L₃.↑✶ k) ≡ L₃.⨀ (σs₂ L₃.↑✶ k)) →
            ∀ k t → t A₁./✶ σs₁ L₃.↑✶ k ≡ t A₁./✶ σs₂ L₃.↑✶ k
  /✶-↑✶′ σs₁ σs₂ hyp = /✶-↑✶ σs₁ σs₂ (λ k x → begin
      L₂.var x A₂./✶ σs₁ L₃.↑✶ k
    ≡⟨ sym (lift-lookup-⨀ x (σs₁ L₃.↑✶ k)) ⟩
      lift (lookup x (L₃.⨀ (σs₁ L₃.↑✶ k)))
    ≡⟨ cong (lift ∘ lookup x) (hyp k) ⟩
      lift (lookup x (L₃.⨀ (σs₂ L₃.↑✶ k)))
    ≡⟨ lift-lookup-⨀ x (σs₂ L₃.↑✶ k) ⟩
      L₂.var x A₂./✶ σs₂ L₃.↑✶ k
    ∎)

  -- Derived lemmas about applications of T₃ substitutions to T₁s.
  appLemmas : AppLemmas T₁ T₃
  appLemmas = record
    { application = application₁₃
    ; lemmas₄     = lemmas₃
    ; id-vanishes = /✶-↑✶′ (ε ▻ L₃.id) ε L₃.id-↑⋆ 0
    ; /-⊙         = /✶-↑✶′ (ε ▻ _ L₃.⊙ _) (ε ▻ _ ▻ _) L₃.↑⋆-distrib 0
    }
  open ExtAppLemmas appLemmas public
    hiding (application; lemmas₂; lemmas₃; var; weaken; subst; simple)

-- Lemmas relating T₂ and T₃ substitutions in T₁.
record LiftSubLemmas (T₁ T₂ T₃ : ℕ → Set) : Set where
  field
    application₁₂ : Application   T₁ T₂
    liftAppLemmas : LiftAppLemmas T₁ T₂ T₃

  open LiftAppLemmas liftAppLemmas hiding (/✶-↑✶; /-wk)
  private
    module L₃  = ExtLemmas₄  lemmas₃
    module L₂  = ExtLemmas₄  lemmas₂
    module A₁₂ = Application application₁₂
    module A₁₃ = Application (AppLemmas.application appLemmas)
    module A₂₃ = Application application₂₃

  field
    -- Weakening commutes with lifting.
    weaken-lift : ∀ {n} (t : T₃ n) → L₂.weaken (lift t) ≡ lift (L₃.weaken t)

    -- Applying a composition of T₂ substitutions to T₁s
    -- corresponds to two consecutive applications.
    /-⊙₂ : ∀ {m n k} {σ₁ : Sub T₂ m n} {σ₂ : Sub T₂ n k} t →
           t A₁₂./ σ₁ L₂.⊙ σ₂ ≡ t A₁₂./ σ₁ A₁₂./ σ₂

    -- Sequences of T₃ substitutions are equivalent to T₂
    -- substitutions when applied to T₁s if they are equivalent when
    -- applied to variables.
    /✶-↑✶₁ :
      ∀ {m n} (σs₁ : Subs T₃ m n) (σs₂ : Subs T₂ m n) →
      (∀ k x → L₂.var x A₂₃./✶ σs₁ ↑✶ k ≡ L₂.var x L₂./✶  σs₂ L₂.↑✶ k) →
       ∀ k t → t        A₁₃./✶ σs₁ ↑✶ k ≡ t        A₁₂./✶ σs₂ L₂.↑✶ k

    -- Sequences of T₃ substitutions are equivalent to T₂
    -- substitutions when applied to T₂s if they are equivalent when
    -- applied to variables.
    /✶-↑✶₂ :
      ∀ {m n} (σs₁ : Subs T₃ m n) (σs₂ : Subs T₂ m n) →
      (∀ k x → L₂.var x A₂₃./✶ σs₁ ↑✶ k ≡ L₂.var x L₂./✶ σs₂ L₂.↑✶ k) →
       ∀ k t → t        A₂₃./✶ σs₁ ↑✶ k ≡ t        L₂./✶ σs₂ L₂.↑✶ k

  -- Lifting of T₃ substitutions to T₂ substitutions.
  liftSub : ∀ {m n} → Sub T₃ m n → Sub T₂ m n
  liftSub σ = map lift σ

  -- The two types of lifting commute.
  liftSub-↑⋆ : ∀ {m n} (σ : Sub T₃ m n) k →
               liftSub σ L₂.↑⋆ k ≡ liftSub (σ ↑⋆ k)
  liftSub-↑⋆ σ zero    = refl
  liftSub-↑⋆ σ (suc k) = cong₂ _∷_ (sym (lift-var _)) (begin
    map L₂.weaken (liftSub σ L₂.↑⋆ k)   ≡⟨ cong (map _) (liftSub-↑⋆ σ k) ⟩
    map L₂.weaken (map lift (σ ↑⋆ k))   ≡⟨ sym (map-∘ _ _ _) ⟩
    map (L₂.weaken ∘ lift) (σ ↑⋆ k)     ≡⟨ map-cong weaken-lift _ ⟩
    map (lift ∘ L₃.weaken)  (σ ↑⋆ k)    ≡⟨ map-∘ _ _ _ ⟩
    map lift (map L₃.weaken (σ ↑⋆ k))   ∎)

  -- The identity substitutions are equivalent up to lifting.
  liftSub-id : ∀ {n} → liftSub (L₃.id {n}) ≡ L₂.id {n}
  liftSub-id {zero}  = refl
  liftSub-id {suc n} = begin
    liftSub (L₃.id L₃.↑)  ≡⟨ sym (liftSub-↑⋆ L₃.id 1) ⟩
    liftSub L₃.id L₂.↑    ≡⟨ cong L₂._↑ liftSub-id ⟩
    L₂.id ∎

  -- Weakening is equivalent up to lifting.
  liftSub-wk⋆ : ∀ k {n} → liftSub (L₃.wk⋆ k {n}) ≡ L₂.wk⋆ k {n}
  liftSub-wk⋆ zero    = liftSub-id
  liftSub-wk⋆ (suc k) = begin
    liftSub (map L₃.weaken (L₃.wk⋆ k))   ≡⟨ sym (map-∘ _ _ _) ⟩
    map (lift ∘ L₃.weaken) (L₃.wk⋆ k)    ≡⟨ sym (map-cong weaken-lift _) ⟩
    map (L₂.weaken ∘ lift) (L₃.wk⋆ k)    ≡⟨ map-∘ _ _ _ ⟩
    map L₂.weaken (liftSub (L₃.wk⋆ k))   ≡⟨ cong (map _) (liftSub-wk⋆ k) ⟩
    map L₂.weaken (L₂.wk⋆ k)             ∎

  -- Weakening is equivalent up to lifting.
  liftSub-wk : ∀ {n} → liftSub (L₃.wk {n}) ≡ L₂.wk {n}
  liftSub-wk = liftSub-wk⋆ 1

  -- Single variable substitution is equivalent up to lifting.
  liftSub-sub : ∀ {n} (t : T₃ n) → liftSub (L₃.sub t) ≡ L₂.sub (lift t)
  liftSub-sub t = cong₂ _∷_ refl liftSub-id

  -- Lifting commutes with application to variables.
  var-/-liftSub-↑⋆ : ∀ {m n} (σ : Sub T₃ m n) k x →
                     L₂.var x A₂₃./ σ ↑⋆ k ≡ L₂.var x L₂./ liftSub σ L₂.↑⋆ k
  var-/-liftSub-↑⋆ σ k x = begin
      L₂.var x A₂₃./ σ ↑⋆ k
    ≡⟨ cong₂ A₂₃._/_ (sym (lift-var x)) refl ⟩
      lift (L₃.var x) A₂₃./ σ ↑⋆ k
    ≡⟨ sym (lift-/ _) ⟩
      lift (L₃.var x L₃./ σ ↑⋆ k)
    ≡⟨ cong lift L₃.var-/ ⟩
      lift (lookup x (σ ↑⋆ k))
    ≡⟨ sym (lookup-map x _ _) ⟩
      lookup x (liftSub (σ ↑⋆ k))
    ≡⟨ sym L₂.var-/ ⟩
      L₂.var x L₂./ liftSub (σ ↑⋆ k)
    ≡⟨ cong (L₂._/_ (L₂.var x)) (sym (liftSub-↑⋆ σ k)) ⟩
      L₂.var x L₂./ liftSub σ L₂.↑⋆ k
    ∎

  -- Lifting commutes with application.
  /-liftSub : ∀ {m n} t {σ : Sub T₃ m n} →
              t A₁₃./ σ ≡ t A₁₂./ liftSub σ
  /-liftSub t {σ} = /✶-↑✶₁ (ε ▻ σ) (ε ▻ liftSub σ)
                           (var-/-liftSub-↑⋆ σ) zero t

  -- Weakening is equivalent up to choice of application.
  /-wk : ∀ {n} {t : T₁ n} → t A₁₃./ L₃.wk ≡ t A₁₂./ L₂.wk
  /-wk {t = t} = begin
    t A₁₃./ L₃.wk           ≡⟨ /-liftSub t ⟩
    t A₁₂./ liftSub L₃.wk   ≡⟨ cong₂ A₁₂._/_ refl liftSub-wk ⟩
    t A₁₂./ L₂.wk           ∎

  -- Single-variable substitution is equivalent up to choice of
  -- application.
  /-sub : ∀ {n} t (s : T₃ n) →
          t A₁₃./ L₃.sub s ≡ t A₁₂./ L₂.sub (lift s)
  /-sub t s = begin
    t A₁₃./ L₃.sub s             ≡⟨ /-liftSub t ⟩
    t A₁₂./ liftSub (L₃.sub s)   ≡⟨ cong₂ A₁₂._/_ refl (liftSub-sub s) ⟩
    t A₁₂./ L₂.sub (lift s)      ∎

  -- Lifting commutes with application.
  /-sub-↑ : ∀ {m n} t s (σ : Sub T₃ m n) →
            t A₁₂./ L₂.sub s A₁₃./ σ ≡ (t A₁₃./ σ ↑) A₁₂./ L₂.sub (s A₂₃./ σ)
  /-sub-↑ t s σ = begin
      t A₁₂./ L₂.sub s A₁₃./ σ
    ≡⟨ /-liftSub _ ⟩
      t A₁₂./ L₂.sub s A₁₂./ liftSub σ
    ≡⟨ sym (/-⊙₂ t) ⟩
      t A₁₂./ (L₂.sub s L₂.⊙ liftSub σ)
    ≡⟨ cong₂ A₁₂._/_ refl (L₂.sub-⊙ s) ⟩
      t A₁₂./ (liftSub σ L₂.↑ L₂.⊙ L₂.sub (s L₂./ liftSub σ))
    ≡⟨ /-⊙₂ t ⟩
      t A₁₂./ liftSub σ L₂.↑ A₁₂./ L₂.sub (s L₂./ liftSub σ)
    ≡⟨ cong₂ (A₁₂._/_ ∘ A₁₂._/_ t) (liftSub-↑⋆ _ 1)
             (cong L₂.sub (sym (/-liftSub₂ s))) ⟩
      t A₁₂./ liftSub (σ ↑) A₁₂./ L₂.sub (s A₂₃./ σ)
    ≡⟨ cong₂ A₁₂._/_ (sym (/-liftSub t)) refl ⟩
      t A₁₃./ σ ↑ A₁₂./ L₂.sub (s A₂₃./ σ)
    ∎
    where
      /-liftSub₂ : ∀ {m n} s {σ : Sub T₃ m n} →
                   s A₂₃./ σ ≡ s L₂./ liftSub σ
      /-liftSub₂ s {σ} = /✶-↑✶₂ (ε ▻ σ) (ε ▻ liftSub σ)
                                (var-/-liftSub-↑⋆ σ) zero s

-- Lemmas for a term-like T₁ derived from term lemmas for T₂
record TermLikeLemmas (T₁ T₂ : ℕ → Set) : Set₁ where
  field
    app         : ∀ {T₃} → Lift T₃ T₂ → ∀ {m n} → T₁ m → Sub T₃ m n → T₁ n
    termLemmas  : TermLemmas T₂

  open TermLemmas termLemmas  using (termSubst)
  open TermSubst  termSubst   using (var; termLift; varLift; module Lifted)

  field /✶-↑✶₁ : ∀ {T₃} {lift : Lift T₃ T₂} →
                 let open Application (record { _/_ = app lift })
                       using ()     renaming (_/✶_ to _/✶₁_)
                     open Lifted lift
                       using (_↑✶_) renaming (_/✶_ to _/✶₂_)
                 in
                 ∀ {m n} (σs₁ : Subs T₃ m n) (σs₂ : Subs T₃ m n) →
                 (∀ k x → var x /✶₂ σs₁ ↑✶ k ≡ var x /✶₂ σs₂ ↑✶ k) →
                  ∀ k t → t     /✶₁ σs₁ ↑✶ k ≡ t     /✶₁ σs₂ ↑✶ k

  termApplication : Application T₁ T₂
  termApplication = record { _/_ = app termLift }

  varApplication : Application T₁ Fin
  varApplication = record { _/_ = app varLift }

  field /✶-↑✶₂ : let open Application varApplication
                       using () renaming (_/✶_ to _/✶₁₃_)
                     open Application termApplication
                       using () renaming (_/✶_ to _/✶₁₂_)
                     open Lifted varLift
                       using () renaming (_↑✶_ to _↑✶₃_; _/✶_ to _/✶₂₃_)
                     open TermSubst termSubst
                       using () renaming (_↑✶_ to _↑✶₂_; _/✶_ to _/✶₂₂_)
                 in
                 ∀ {m n} (σs₁ : Subs Fin m n) (σs₂ : Subs T₂ m n) →
                 (∀ k x → var x /✶₂₃ σs₁ ↑✶₃ k ≡ var x /✶₂₂ σs₂ ↑✶₂ k) →
                  ∀ k t → t     /✶₁₃ σs₁ ↑✶₃ k ≡ t     /✶₁₂ σs₂ ↑✶₂ k

  -- An instantiation of the above lemmas for T₂ substitutions in T₁s.
  termLiftAppLemmas : LiftAppLemmas T₁ T₂ T₂
  termLiftAppLemmas = record
    { lift          = Lift.lift termLift
    ; application₁₃ = termApplication
    ; application₂₃ = TermLemmas.application termLemmas
    ; lemmas₂       = TermLemmas.lemmas₄ termLemmas
    ; lemmas₃       = TermLemmas.lemmas₄ termLemmas
    ; lift-/        = λ _ → refl
    ; lift-var      = λ _ → refl
    ; /✶-↑✶         = /✶-↑✶₁
    }

  open LiftAppLemmas termLiftAppLemmas public hiding (/-wk)

  -- An instantiation of the above lemmas for variable substitutions
  -- (renamings) in T₁s.
  varLiftSubLemmas : LiftSubLemmas T₁ T₂ Fin
  varLiftSubLemmas = record
    { application₁₂ = termApplication
    ; liftAppLemmas = record
      { lift          = Lift.lift varLift
      ; application₁₃ = varApplication
      ; application₂₃ = Lifted.application varLift
      ; lemmas₂       = TermLemmas.lemmas₄ termLemmas
      ; lemmas₃       = VarLemmas.lemmas₄
      ; lift-/        = λ _ → sym (TermLemmas.app-var termLemmas)
      ; lift-var      = λ _ → refl
      ; /✶-↑✶         = /✶-↑✶₁
      }
    ; weaken-lift = λ _ → TermLemmas.weaken-var termLemmas
    ; /-⊙₂        = AppLemmas./-⊙ appLemmas
    ; /✶-↑✶₁      = /✶-↑✶₂
    ; /✶-↑✶₂      = TermLemmas./✶-↑✶ termLemmas
    }

  open Application   varApplication   public using () renaming (_/_ to _/Var_)
  open LiftSubLemmas varLiftSubLemmas public hiding (/✶-↑✶₁; /✶-↑✶₂)
    renaming (liftAppLemmas to varLiftAppLemmas)

  -- Weakening of T₁s.
  weaken : ∀ {n} → T₁ n → T₁ (suc n)
  weaken t = t /Var VarSubst.wk

  -- A version of wk-sub-vanishes for T₁s.
  weaken-sub : ∀ {n t′} → (t : T₁ n) → weaken t / sub t′ ≡ t
  weaken-sub t = begin
    weaken t / sub _   ≡⟨ cong₂ _/_ /-wk refl ⟩
    t / wk / sub _     ≡⟨ wk-sub-vanishes t ⟩
    t                  ∎
