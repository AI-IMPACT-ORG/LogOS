{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Minimal.ScaleOps where

open import LogOS.Prelude
open import LogOS.Prelude.Nat using (ℕ)
open import LogOS.Prelude.NatOrder using (_≤ℕ_)

open import LogOS.Minimal.Adapter using (QAdapter)

-- Operational view of a scale: interpret grades as step budgets.
-- This is intentionally lightweight; laws live in downstream assumptions.

record ScaleOps {ℓ : Level} (Q : QAdapter ℓ) : Set (lsuc ℓ) where
  open QAdapter Q
  field
    budget : Scale → Time
    steps  : Time → ℕ

-- Optional strengthening: monotonicity of the operational step budget.
--
-- This is the minimal law needed to reason “more budget ⇒ at least as many
-- steps” without assuming anything about `Time` itself.
record ScaleOpsLaws {ℓ : Level} (Q : QAdapter ℓ) (Ops : ScaleOps Q) : Set (lsuc ℓ) where
  open QAdapter Q
  open ScaleOps Ops
  field
    steps-budget-mono
      : ∀ {g g'}
      → g ≤s g'
      → steps (budget g) ≤ℕ steps (budget g')

-- Common packaging: an operational view together with its monotonicity law.
record BudgetOps {ℓ : Level} (Q : QAdapter ℓ) : Set (lsuc ℓ) where
  field
    Ops  : ScaleOps Q
    laws : ScaleOpsLaws Q Ops

  open ScaleOps Ops public
  open ScaleOpsLaws laws public
