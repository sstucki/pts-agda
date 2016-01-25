------------------------------------------------------------------------
-- Pure type systems (PTS)
------------------------------------------------------------------------

-- This file contains some core definitions which are reexported by
-- Pts.Typing

module Pts.Core where

open import Data.Fin.Substitution.Typed
open import Data.Product using (∃)

import Pts.Syntax

-- Instances of pure type systems.
record PTS : Set₁ where

  -- The following predicates represent the set of sorts, axioms and
  -- rules, respectively.
  field
    Sort  : Set                        -- sorts
    Axiom : Sort → Sort → Set          -- axioms
    Rule  : Sort → Sort → Sort → Set   -- rules

  -- Convenience aliases of modules in Pts.Syntax.
  module Syntax       = Pts.Syntax.Syntax       Sort
  module Substitution = Pts.Syntax.Substitution Sort
  module Ctx          = Pts.Syntax.Ctx          Sort

  open Syntax

  -- Abstract well-formed typing contexts.
  module WfCtx (_⊢_∈_ : Typing Term Term Term) where

    -- Well-formedness of terms/types.
    _⊢_wf : Wf Term
    Γ ⊢ a wf = ∃ λ s → Γ ⊢ a ∈ sort s
    open WellFormedContext _⊢_wf public
