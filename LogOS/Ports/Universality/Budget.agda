{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Universality.Budget where

-- Budget readout slice over `OpacityPort`: explicit cost/fuel observation and
-- transport obligations.
--
-- The critical rule is that budget transport is an explicit contract, not an
-- inference from surrounding code.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_)
open import LogOS.LT.View using (View; μ)
open import LogOS.LT.Kernel using (Kernel; Code)
open import LogOS.LT.Hom.Core using (KernelHom; mapCode)
import LogOS.Ports.Opacity.Port as Opacity

BudgetPort
  : ∀ {ℓCode ℓBudgetCon ℓBudgetRel : Level}
  → (CodeType : Set ℓCode)
  → (BudgetBoundary : ConPreorder ℓBudgetCon ℓBudgetRel)
  → Set (lsuc (ℓCode ⊔ ℓBudgetCon ⊔ ℓBudgetRel))
BudgetPort = Opacity.OpacityPort

budgetObservation = Opacity.toView

budgetReadout
  : ∀ {ℓCode ℓBudgetCon ℓBudgetRel}
    {CodeType : Set ℓCode}
    {BudgetBoundary : ConPreorder ℓBudgetCon ℓBudgetRel}
  → BudgetPort CodeType BudgetBoundary
  → CodeType
  → Con BudgetBoundary
budgetReadout budgetPort sourceCode = μ (Opacity.toView budgetPort) sourceCode

record BudgetTransport
  {ℓKernelCon ℓKernelRel ℓCode ℓBudgetCon ℓBudgetRel : Level}
  {K K' : Kernel ℓKernelCon ℓKernelRel ℓCode}
  {Budget : ConPreorder ℓBudgetCon ℓBudgetRel}
  (sourceBudget : BudgetPort (Code K) Budget)
  (targetBudget : BudgetPort (Code K') Budget)
  (translator : KernelHom K K')
  : Set (lsuc (ℓCode ⊔ ℓKernelRel ⊔ ℓBudgetCon ⊔ ℓBudgetRel)) where
  field
    budget-monotone
      : ∀ sourceCode →
        ConPreorder._⊑_ Budget
          (budgetReadout targetBudget (mapCode translator sourceCode))
          (budgetReadout sourceBudget sourceCode)
