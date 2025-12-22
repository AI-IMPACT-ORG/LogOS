{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Computation.Core where

open import LogOS.Prelude

-- Minimal computation interface: a code carrier with a total step.

record Computation {ℓ : Level} (Code : Set ℓ) : Set (lsuc ℓ) where
  field
    Step  : Code → Code
    Halts : Code → Set ℓ         -- halting predicate (model-chosen)

open Computation public

iterate : ∀ {ℓ Code} → Computation {ℓ} Code → ℕ → Code → Code
iterate C zero    c = c
iterate C (suc n) c = iterate C n (Computation.Step C c)
