{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Valuation.QAdapterBudgetTransport2Cat where

-- Time-graded budget transport as a displayed layer over LOG.
--
-- This is the port totalisation/2-category packaging corresponding to the
-- algebraic definitions in `LogOS.Ports.Valuation.QAdapterBudgetTransport`.
--
-- Design discipline:
-- keep this module focused on displayed/Σ-totalisation plumbing; keep iteration
-- bounds and transport algebra in the non-`*2Cat` module.

open import LogOS.Prelude
open import LogOS.LT.Kernel using (Kernel; Code)
open import LogOS.LT.Hom.Core using (KernelHom; idKernelHom; _∘_)
open import LogOS.LT.LOG.Kernel2Cat using (LOG)
open import LogOS.LT.DisplayedThin2Cat using (DisplayedThin2Cat)

open import LogOS.Ports.Universality.Budget using (BudgetPort)
open import LogOS.Ports.Valuation.QAdapter using (QAdapter; QClock)
open import LogOS.Ports.Valuation.ScaleBoundary using (ScaleBoundary)

import LogOS.Ports.Valuation.QAdapterBudgetTransport as Transport

import LogOS.LT.Ports.PortSig as PortSig
import LogOS.LT.Ports.Template.Singleton2Cat as Template

data TimeBudgetTag : Set where
  timeBudgetTag : TimeBudgetTag

timeBudgetTagId : ℕ
timeBudgetTagId = 17

mkBudgetDisplayed
  : ∀ {ℓKernelCon ℓKernelRel ℓCode ℓQ ℓDHom : Level}
  → (Q : QAdapter ℓQ)
  → (HomBudget
      : ∀ {K K' : Kernel ℓKernelCon ℓKernelRel ℓCode}
      → (h : KernelHom K K')
      → BudgetPort (Code K) (ScaleBoundary Q)
      → BudgetPort (Code K') (ScaleBoundary Q)
      → Set ℓDHom)
  → (idBudget
      : ∀ {K : Kernel ℓKernelCon ℓKernelRel ℓCode}
      → (BK : BudgetPort (Code K) (ScaleBoundary Q))
      → HomBudget (idKernelHom K) BK BK)
  → (compBudget
      : ∀ {K₁ K₂ K₃ : Kernel ℓKernelCon ℓKernelRel ℓCode}
        {f : KernelHom K₁ K₂}
        {g : KernelHom K₂ K₃}
        {BK₁ : BudgetPort (Code K₁) (ScaleBoundary Q)}
        {BK₂ : BudgetPort (Code K₂) (ScaleBoundary Q)}
        {BK₃ : BudgetPort (Code K₃) (ScaleBoundary Q)}
      → HomBudget f BK₁ BK₂
      → HomBudget g BK₂ BK₃
      → HomBudget (g ∘ f) BK₁ BK₃)
  → DisplayedThin2Cat
      (LOG {ℓKernelCon} {ℓKernelRel} {ℓCode})
      (lsuc (ℓCode ⊔ ℓQ))
      ℓDHom
mkBudgetDisplayed Q HomBudget idBudget compBudget =
  record
    { Ob = λ K → BudgetPort (Code K) (ScaleBoundary Q)
    ; HomD = λ {K} {K'} h BK BK' → HomBudget h BK BK'
    ; idD = idBudget
    ; compD = λ tf tg → compBudget tf tg
    }

GradedBudgetDisplayed
  : ∀ {ℓKernelCon ℓKernelRel ℓCode ℓQ : Level}
  → (Q : QAdapter ℓQ)
  → DisplayedThin2Cat
      (LOG {ℓKernelCon} {ℓKernelRel} {ℓCode})
      (lsuc (ℓCode ⊔ ℓQ))
      (lsuc (ℓCode ⊔ ℓQ))
GradedBudgetDisplayed {ℓKernelCon} {ℓKernelRel} {ℓCode} Q =
  mkBudgetDisplayed
    {ℓKernelCon} {ℓKernelRel} {ℓCode}
    Q
    (λ h BK BK' → Transport.QBudgetTransport Q BK BK' h)
    (Transport.idQBudgetTransport Q)
    (Transport.composeQBudgetTransport Q)

TimeBudgetDisplayed
  : ∀ {ℓKernelCon ℓKernelRel ℓCode ℓQ : Level}
  → (Q : QAdapter ℓQ)
  → (T : QClock Q)
  → DisplayedThin2Cat
      (LOG {ℓKernelCon} {ℓKernelRel} {ℓCode})
      (lsuc (ℓCode ⊔ ℓQ))
      (lsuc (ℓCode ⊔ ℓQ))
TimeBudgetDisplayed {ℓKernelCon} {ℓKernelRel} {ℓCode} Q T =
  mkBudgetDisplayed
    {ℓKernelCon} {ℓKernelRel} {ℓCode}
    Q
    (λ h BK BK' → Transport.QTimeBudgetTransport Q T BK BK' h)
    (Transport.idQTimeBudgetTransport Q T)
    (Transport.composeQTimeBudgetTransport Q T)

module Port
  {ℓKernelCon ℓKernelRel ℓCode ℓQ : Level}
  (Q : QAdapter ℓQ)
  (T : QClock Q)
  = Template.SingletonLayer
      timeBudgetTagId
      {Tag = TimeBudgetTag}
      (TimeBudgetDisplayed {ℓKernelCon} {ℓKernelRel} {ℓCode} Q T)

timeBudgetSig
  : ∀ {ℓKernelCon ℓKernelRel ℓCode ℓQ : Level}
  → (Q : QAdapter ℓQ)
  → (T : QClock Q)
  → PortSig.PortSig (LOG {ℓKernelCon} {ℓKernelRel} {ℓCode}) timeBudgetTagId TimeBudgetTag
timeBudgetSig {ℓKernelCon} {ℓKernelRel} {ℓCode} {ℓQ} Q T =
  Port.portSig {ℓKernelCon} {ℓKernelRel} {ℓCode} {ℓQ} Q T

open Port public using
  ( port2Cat
  ; singleton
  ; stack
  ; port
  ; Displayed
  ; WithPort
  ; forget
  )
