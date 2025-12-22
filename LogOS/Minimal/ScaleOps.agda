{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Minimal.ScaleOps where

open import LogOS.Prelude
open import Data.Nat using (ℕ)

open import LogOS.Minimal.Adapter using (QAdapter)

-- Operational view of a scale: interpret grades as step budgets.
-- This is intentionally lightweight; laws live in downstream assumptions.

record ScaleOps {ℓ : Level} (Q : QAdapter ℓ) : Set (lsuc ℓ) where
  open QAdapter Q
  field
    budget : Scale → Time
    steps  : Time → ℕ
