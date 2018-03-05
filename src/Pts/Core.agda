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
  open Ctx

  -- Abstract well-formed typing contexts.
  module WfCtx (_⊢_∈_ : Typing Term Term Term) where

    -- Well-formedness of terms/types.
    _⊢_wf : Wf Term
    Γ ⊢ a wf = ∃ λ s → Γ ⊢ a ∈ sort s

    -- FIXME: the following definition should not be necessary.
    --
    -- Instead, it should be sufficient to directly open the module
    -- WellFormedContext like so:
    --
    --   open WellFormedContext _⊢_wf public
    --
    -- but there is currently a bug that prevents us from doing so.
    -- See https://github.com/agda/agda/issues/2901

    _wf : ∀ {n} → Ctx n → Set
    _wf = WellFormedContext._wf  _⊢_wf

    open WellFormedContext _⊢_wf public hiding (_wf)
