------------------------------------------------------------------------
-- Progress of CBV reductions in pure type systems (PTS)
------------------------------------------------------------------------

-- This module contains a variant of the "progress" theorem for PTS.
-- Progress says roughly that well-typed terms do not get stuck.
-- I.e. a well-typed term is either a value or it can take a CBV
-- reduction step.  Together with the subject reduction (aka
-- "preservation") theorem from Pts.Typing, progress ensures type
-- soundness.  For detials, see e.g.
--
--  * B. C. Pierce, TAPL (2002), pp. 95.
--
--  * A. Wright and M. Felleisen, "A Syntactic Approach to Type
--    Soundness" (1994).

module Pts.Typing.Progress where

open import Data.Product using (_,_; ∃; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)

open import Pts.Typing
open import Pts.Reduction.Cbv
open import Pts.Reduction.Full


-- Definitions and lemmas are parametrized by a given PTS instance.
module _ {pts} where
  open PTS pts
  open Syntax
  open Ctx
  open Substitution using (_[_])
  open Typing pts

  -- A helper lemma: sorts are not product types.
  Π≢sort : ∀ {n s} {a : Term n} {b} → ¬ (Π a b ≡β sort s)
  Π≢sort Πab≡s =
    let _ , Πab→*c , s→*c       = ≡β⇒→β* Πab≡s
        _ , _ , _ , _ , Πa′b′≡c = Π-→β* Πab→*c
    in contradiction Πa′b′≡c (sort⇒¬Π (sort-→β* s→*c))
    where
      sort⇒¬Π : ∀ {n s a b} {c : Term n} → sort s ≡ c → ¬ (Π a b ≡ c)
      sort⇒¬Π refl ()

  -- A canonical forms lemma for dependent product values: closed
  -- values of product type are abstractions.
  Π-can : ∀ {f a b} → Val f → [] ⊢ f ∈ Π a b → ∃ λ a′ → ∃ λ t → f ≡ ƛ a′ t
  Π-can (sort s) s∈Πab =
    let _ , _ , Πab≡s′ = sort-gen s∈Πab
    in contradiction Πab≡s′ Π≢sort
  Π-can (Π c d)  Πcd∈Πab =
    let _ , _ , _ , _ , _ , _ , Πab≡s = Π-gen Πcd∈Πab
    in contradiction Πab≡s Π≢sort
  Π-can (ƛ a′ t) (ƛ a∈s t∈b)             = a′ , t , refl
  Π-can (ƛ a′ t) (conv λa′t∈c c∈s c≡Πab) = a′ , t , refl

  -- Progress: well-typed terms do not get stuck (under CBV reduction).
  prog : ∀ {a b} → [] ⊢ a ∈ b → Val a ⊎ (∃ λ a′ → a →v a′)
  prog (var () Γ-wf)
  prog (axiom a Γ-wf)  = inj₁ (sort _)
  prog (Π r a∈s₁ b∈s₂) = inj₁ (Π _ _)
  prog (ƛ t∈b Πab∈s)   = inj₁ (ƛ _ _)
  prog (f∈Πab · t∈a)   with prog f∈Πab
  prog (f∈Πab · t∈a)   | inj₁ u with prog t∈a
  prog (f∈Πab · t∈a)   | inj₁ u | inj₁ v with Π-can u f∈Πab
  ...| a′ , t′ , refl = inj₂ (_ , cont a′ t′ v)
  prog (f∈Πab · t∈a)   | inj₁ u | inj₂ (t′ , t→t′) = inj₂ (_ , u ·₂ t→t′)
  prog (f∈Πab · t∈a)   | inj₂ (f′ , f→f′) = inj₂ (_ , f→f′ ·₁ _)
  prog (conv a∈b₁ b₂∈s b₁≡b₂) = prog a∈b₁
