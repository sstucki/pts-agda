------------------------------------------------------------------------
-- Experiments with Pure Type Systems (PTS)
------------------------------------------------------------------------

-- Author: Sandro Stucki
-- Copyright (c) 2015 EPFL

-- The code in this directory contains a (partial) Agda formalization
-- of Pure Type Systems (PTS).
--
-- The code makes heavy use of the Agda standard library, which is
-- freely available from
--
--   https://github.com/agda/agda-stdlib/
--
-- The code has been tested using Agda 2.5.3 and version 0.14 of the
-- Agda standard library.


module README where

------------------------------------------------------------------------
-- Modules related to pure type systems (PTS)

-- Syntax of (untyped) terms along with support for substitutions.
open import Pts.Syntax

-- Variants of β-reduction/equivalence and properties thereof.
open import Pts.Reduction.Cbv
open import Pts.Reduction.Full
open import Pts.Reduction.Parallel

-- Typing of terms, substitution lemmas and a proofs of type soundess
-- (preservation/subject reduction and progress).
open import Pts.Core
open import Pts.Typing
open import Pts.Typing.Progress


------------------------------------------------------------------------
-- Modules containing generic functionality

-- Extra lemmas that are derivable in the substitution framework of
-- the Agda standard library, as well as support for substitutions
-- lifted to relations and typed substitutions.
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Fin.Substitution.Relation
open import Data.Fin.Substitution.Typed

-- Symmetric and equivalence closures of binary relations.
open import Relation.Binary.SymmetricClosure
open import Relation.Binary.EquivalenceClosure

-- Support for generic reduction relations.
open import Relation.Binary.Reduction
