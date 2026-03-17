{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Universality.BudgetBus2Cat where

-- Budget-equipped kernels as a thin 2-category (LOGᵇ).
-- (A Σ-decoration (Grothendieck-style; refinement inherited from the base) of a displayed structure over `LOG`.)
--
-- Displayed objects: a `BudgetPort` into a fixed budget boundary preorder.
-- Displayed morphisms: explicit budget transport obligations (`BudgetTransport`).
-- 2-cells: inherited boundary-driven observational refinements (`_⇒∂_`) on the underlying kernel morphisms.
--
-- This is the general “numeric bus” layer; a `QAdapter` specializes it by
-- choosing the budget boundary to be its scale preorder (see `LogOS.Ports.Valuation.QAdapterBus`).

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; refl⊑)
open import LogOS.LT.Kernel using (Kernel; Code)
open import LogOS.LT.Hom.Core using (KernelHom; idKernelHom; _∘_; mapCode)
open import LogOS.LT.DisplayedThin2Cat using (DisplayedThin2Cat)
open import LogOS.LT.LOG.Kernel2Cat using (LOG)
open import LogOS.Ports.Universality.Budget using (BudgetPort; BudgetTransport; budgetReadout)
private
  module ≤-Reasoning = LogOS.Prelude.RefinementKit.Reasoning

import LogOS.LT.Ports.PortSig as PortSig
import LogOS.LT.Ports.Template.Singleton2Cat as Template

data BudgetTag : Set where
  budgetTag : BudgetTag

budgetTagId : ℕ
budgetTagId = 18

idBudgetTransport
  : ∀ {ℓ ℓRel ℓCode ℓBudgetCon ℓBudgetRel : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {Budget : ConPreorder ℓBudgetCon ℓBudgetRel}
  → (BK : BudgetPort (Code K) Budget)
  → BudgetTransport BK BK (idKernelHom K)
idBudgetTransport {Budget = Budget} _ =
  record { budget-monotone = λ _ → refl⊑ Budget }

composeBudgetTransport
  : ∀ {ℓ ℓRel ℓCode ℓBudgetCon ℓBudgetRel : Level}
    {K₁ K₂ K₃ : Kernel ℓ ℓRel ℓCode}
    {Budget : ConPreorder ℓBudgetCon ℓBudgetRel}
    {f : KernelHom K₁ K₂}
    {g : KernelHom K₂ K₃}
    {BK₁ : BudgetPort (Code K₁) Budget}
    {BK₂ : BudgetPort (Code K₂) Budget}
    {BK₃ : BudgetPort (Code K₃) Budget}
  → BudgetTransport BK₁ BK₂ f
  → BudgetTransport BK₂ BK₃ g
  → BudgetTransport BK₁ BK₃ (g ∘ f)
composeBudgetTransport {Budget = Budget} {f = f} {g = g} {BK₁ = BK₁} {BK₂ = BK₂} {BK₃ = BK₃} tf tg =
  record
    { budget-monotone =
        λ sourceCode →
          let
            module R = ≤-Reasoning Budget
            open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
          in
          begin⊑
            budgetReadout BK₃ (mapCode g (mapCode f sourceCode))
              ⊑⟨ BudgetTransport.budget-monotone tg (mapCode f sourceCode) ⟩
            budgetReadout BK₂ (mapCode f sourceCode)
              ⊑⟨ BudgetTransport.budget-monotone tf sourceCode ⟩
            budgetReadout BK₁ sourceCode ∎⊑
    }

BudgetDisplayed
  : ∀ {ℓ ℓRel ℓCode ℓBudgetCon ℓBudgetRel : Level}
  → (Budget : ConPreorder ℓBudgetCon ℓBudgetRel)
  → DisplayedThin2Cat
      (LOG {ℓ} {ℓRel} {ℓCode})
      (lsuc (ℓCode ⊔ ℓBudgetCon ⊔ ℓBudgetRel))
      (lsuc (ℓCode ⊔ ℓRel ⊔ ℓBudgetCon ⊔ ℓBudgetRel))
BudgetDisplayed {ℓ} {ℓRel} {ℓCode} Budget =
  record
    { Ob = λ K → BudgetPort (Code K) Budget
    ; HomD = λ {K} {K'} (h : KernelHom K K') BK BK' → BudgetTransport BK BK' h
    ; idD = idBudgetTransport
    ; compD = λ tf tg → composeBudgetTransport tf tg
    }

module Port {ℓ ℓRel ℓCode ℓBudgetCon ℓBudgetRel : Level}
  (Budget : ConPreorder ℓBudgetCon ℓBudgetRel)
  = Template.SingletonLayer
      budgetTagId
      {Tag = BudgetTag}
      (BudgetDisplayed {ℓ} {ℓRel} {ℓCode} Budget)

budgetSig
  : ∀ {ℓ ℓRel ℓCode ℓBudgetCon ℓBudgetRel : Level}
  → (Budget : ConPreorder ℓBudgetCon ℓBudgetRel)
  → PortSig.PortSig (LOG {ℓ} {ℓRel} {ℓCode}) budgetTagId BudgetTag
budgetSig {ℓ} {ℓRel} {ℓCode} {ℓBudgetCon} {ℓBudgetRel} Budget =
  Port.portSig {ℓ} {ℓRel} {ℓCode} {ℓBudgetCon} {ℓBudgetRel} Budget

open Port public using
  ( port2Cat
  ; singleton
  ; stack
  ; port
  ; Displayed
  ; WithPort
  ; forget
  )
