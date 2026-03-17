{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Valuation.QAdapterBus where

-- A `QAdapter`-specialised “numeric bus” for kernels and translations.
--
-- The v1.1 kernel core stays minimal; this module makes numerics explicit by:
-- - deriving a budget boundary preorder from a chosen `QAdapter` (its scale order),
-- - equipping kernels with budget ports into that boundary, and
-- - transporting those budgets along kernel morphisms via explicit contracts.

open import LogOS.Prelude using (Level; lsuc; _⊔_; _≡_; refl)
open import LogOS.LT.ConPreorder using (ConPreorder; Con)
open import LogOS.LT.Kernel using (Kernel; Code)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Thin2Functor using (Thin2Functor)
open import LogOS.LT.LOG.Kernel2Cat using (LOG)
open import LogOS.Ports.Valuation.QAdapter using (QAdapter)
open import LogOS.Ports.Valuation.ScaleBoundary using (ScaleBoundary)
open import LogOS.Ports.Universality.Budget using (BudgetPort)

import LogOS.LT.Ports.PortStack.Raw as PortStack
import LogOS.Ports.Universality.BudgetBus2Cat as BudgetBus

-- The canonical budget boundary induced by a `QAdapter` (its scale preorder).
QBudget : ∀ {ℓQ : Level} → QAdapter ℓQ → ConPreorder ℓQ ℓQ
QBudget = ScaleBoundary

QBudgetPort
  : ∀ {ℓ ℓRel ℓCode ℓQ : Level}
  → (Q : QAdapter ℓQ)
  → Kernel ℓ ℓRel ℓCode
  → Set (lsuc (ℓCode ⊔ ℓQ ⊔ ℓQ))
QBudgetPort Q K = BudgetPort (Code K) (QBudget Q)

QKernel
  : ∀ {ℓ ℓRel ℓCode ℓQ : Level}
  → (Q : QAdapter ℓQ)
  → Set (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode) ⊔ lsuc (ℓCode ⊔ ℓQ ⊔ ℓQ))
QKernel {ℓ} {ℓRel} {ℓCode} Q =
  Thin2Cat.Obj (BudgetBus.WithPort {ℓ} {ℓRel} {ℓCode} (QBudget Q))

-- Uniform decorated-kernel projection vocabulary.
kernel
  : ∀ {ℓ ℓRel ℓCode ℓQ : Level}
  → (Q : QAdapter ℓQ)
  → QKernel {ℓ} {ℓRel} {ℓCode} Q
  → Kernel ℓ ℓRel ℓCode
kernel {ℓ} {ℓRel} {ℓCode} Q =
  PortStack.baseObj {S = BudgetBus.stack {ℓ} {ℓRel} {ℓCode} (QBudget Q)}

port
  : ∀ {ℓ ℓRel ℓCode ℓQ : Level}
  → (Q : QAdapter ℓQ)
  → (X : QKernel {ℓ} {ℓRel} {ℓCode} Q)
  → QBudgetPort Q (kernel Q X)
port {ℓ} {ℓRel} {ℓCode} Q =
  PortStack.getObj (BudgetBus.port {ℓ} {ℓRel} {ℓCode} (QBudget Q))

QKernelHom
  : ∀ {ℓ ℓRel ℓCode ℓQ : Level}
  → (Q : QAdapter ℓQ)
  → QKernel {ℓ} {ℓRel} {ℓCode} Q
  → QKernel {ℓ} {ℓRel} {ℓCode} Q
  → Set
      (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode) ⊔ lsuc (ℓCode ⊔ ℓRel ⊔ ℓQ ⊔ ℓQ))
QKernelHom {ℓ} {ℓRel} {ℓCode} Q =
  λ X Y → Con (Thin2Cat.Hom (BudgetBus.WithPort {ℓ} {ℓRel} {ℓCode} (QBudget Q)) X Y)

-- The thin 2-category of kernels with a `Q`-budget bus.
LOGQ
  : ∀ {ℓ ℓRel ℓCode ℓQ : Level}
  → (Q : QAdapter ℓQ)
  → Thin2Cat
      (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode) ⊔ lsuc (ℓCode ⊔ ℓQ ⊔ ℓQ))
      (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode) ⊔ lsuc (ℓCode ⊔ ℓRel ⊔ ℓQ ⊔ ℓQ))
      (ℓCode ⊔ ℓRel)
LOGQ {ℓ} {ℓRel} {ℓCode} Q = BudgetBus.WithPort {ℓ} {ℓRel} {ℓCode} (QBudget Q)

forgetQ
  : ∀ {ℓ ℓRel ℓCode ℓQ : Level}
  → (Q : QAdapter ℓQ)
  → Thin2Functor (LOGQ {ℓ} {ℓRel} {ℓCode} Q) (LOG {ℓ} {ℓRel} {ℓCode})
forgetQ {ℓ} {ℓRel} {ℓCode} Q = BudgetBus.forget {ℓ} {ℓRel} {ℓCode} (QBudget Q)

LOGQ≡
  : ∀ {ℓ ℓRel ℓCode ℓQ : Level}
  → (Q : QAdapter ℓQ)
  → LOGQ {ℓ} {ℓRel} {ℓCode} Q
    ≡ BudgetBus.WithPort {ℓ} {ℓRel} {ℓCode} (QBudget Q)
LOGQ≡ _ = refl

forgetQ≡
  : ∀ {ℓ ℓRel ℓCode ℓQ : Level}
  → (Q : QAdapter ℓQ)
  → forgetQ {ℓ} {ℓRel} {ℓCode} Q
    ≡ BudgetBus.forget {ℓ} {ℓRel} {ℓCode} (QBudget Q)
forgetQ≡ _ = refl
