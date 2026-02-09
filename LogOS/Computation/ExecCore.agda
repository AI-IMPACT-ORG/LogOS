{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Computation.ExecCore where

open import LogOS.Prelude
open import LogOS.Minimal.Adapter using (QAdapter)

-- Shared execution-cost fold:
-- execute `n` steps, multiplying one-step costs in the adapter's scale.
costExec
  : ∀ {ℓS ℓQ : Level} {State : Set ℓS}
    (Q : QAdapter ℓQ)
  → (step : State → State)
  → (stepCost : State → QAdapter.Scale Q)
  → ℕ
  → State
  → QAdapter.Scale Q
costExec Q step stepCost zero    s = QAdapter.e Q
costExec Q step stepCost (suc n) s =
  QAdapter._·_ Q (stepCost s) (costExec Q step stepCost n (step s))
