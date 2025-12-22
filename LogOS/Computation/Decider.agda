{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Computation.Decider where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import Data.Sum using (_⊎_)

-- A lightweight notion of a total decider for a predicate P.
--
-- The `decide` carrier is kept abstract (it may be P itself, a boolean witness,
-- a proof object, etc.) but must be total and logically equivalent to P via
-- soundness and completeness.

record Decider {ℓA ℓP : Level} (A : Set ℓA) (P : A → Set ℓP)
              : Set (lsuc (ℓA ⊔ ℓP)) where
  field
    decide : A → Set ℓP
    total  : ∀ x → decide x ⊎ ¬ decide x
    sound  : ∀ x → decide x → P x
    comp   : ∀ x → P x → decide x

open Decider public

