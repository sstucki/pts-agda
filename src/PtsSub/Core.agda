------------------------------------------------------------------------
-- Pure type systems with subtyping (PTS-≤)
------------------------------------------------------------------------

-- This file contains some core definitions which are reexported by
-- PtsSub.Typing

module PtsSub.Core where

open import Data.Fin.Substitution.Typed
open import Data.Product using (∃)

import PtsSub.Syntax

-- Instances of pure type systems with subtyping.
record PTS-≤ : Set₁ where

  -- The following predicates represent the set of sorts, axioms and
  -- rules, respectively.
  field
    Sort   : Set                        -- sorts
    Axiom  : Sort → Sort → Set          -- axioms
    Π-Rule : Sort → Sort → Sort → Set   -- rules for product formation
    …-Rule : Sort → Sort → Set          -- rules for interval formation

  -- Convenience aliases of modules in Pts.Syntax.
  module Syntax       = PtsSub.Syntax.Syntax       Sort
  module Substitution = PtsSub.Syntax.Substitution Sort
  module Ctx          = PtsSub.Syntax.Ctx          Sort

  open Syntax

  -- Abstract well-formed typing contexts.
  module WfCtx (_⊢_∈_ : Typing Term Term Term) where

    -- Well-formedness of terms/types.
    _⊢_wf : Wf Term
    Γ ⊢ a wf = ∃ λ s → Γ ⊢ a ∈ sort s
    open WellFormedContext _⊢_wf public
