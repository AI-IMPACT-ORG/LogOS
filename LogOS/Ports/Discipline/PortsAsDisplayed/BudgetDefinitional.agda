{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Discipline.PortsAsDisplayed.BudgetDefinitional where

open import LogOS.Prelude using (Level; _≡_)
open import LogOS.LT.ConPreorder using (ConPreorder)
open import LogOS.LT.DisplayedThin2Cat using
  ( DecoratedThin2Cat
  ; forgetDecorated
  )
open import LogOS.Ports.Valuation.QAdapter using (QAdapter; QClock)

import LogOS.Ports.Universality.BudgetBus2Cat as BudgetBus
import LogOS.Ports.Universality.FlowBudget2Cat as FlowBudget
import LogOS.Ports.Universality.FlowBudget2CatDefinitional as FlowBudgetDef
import LogOS.Ports.Valuation.QAdapterBus as QBus
import LogOS.Ports.Valuation.QAdapterBudgetTransport2Cat as QTransport
import LogOS.LT.Ports.Template.Singleton2CatDefinitional as SingletonDef
import LogOS.LT.Ports.Template.Stack2CatDefinitional as StackDef

LOGᵇ-def
  : ∀ {ℓ ℓRel ℓCode ℓBudgetCon ℓBudgetRel : Level}
    (Budget : ConPreorder ℓBudgetCon ℓBudgetRel)
  → BudgetBus.WithPort {ℓ} {ℓRel} {ℓCode} Budget
    ≡
    DecoratedThin2Cat (BudgetBus.BudgetDisplayed {ℓ} {ℓRel} {ℓCode} Budget)
LOGᵇ-def Budget = SingletonDef.withPort≡ (BudgetBus.port2Cat Budget)

forgetBudget-def
  : ∀ {ℓ ℓRel ℓCode ℓBudgetCon ℓBudgetRel : Level}
    (Budget : ConPreorder ℓBudgetCon ℓBudgetRel)
  → BudgetBus.forget {ℓ} {ℓRel} {ℓCode} Budget
    ≡
    forgetDecorated (BudgetBus.BudgetDisplayed {ℓ} {ℓRel} {ℓCode} Budget)
forgetBudget-def Budget = SingletonDef.forget≡ (BudgetBus.port2Cat Budget)

FlowBudgetDisplayed-def = FlowBudgetDef.Displayed-product

LOGᶠᵇ-def
  : ∀ {ℓ ℓRel ℓCode ℓBudgetCon ℓBudgetRel : Level}
    (Budget : ConPreorder ℓBudgetCon ℓBudgetRel)
  → FlowBudget.WithPort {ℓ} {ℓRel} {ℓCode} Budget
    ≡
    DecoratedThin2Cat (FlowBudget.Displayed {ℓ} {ℓRel} {ℓCode} Budget)
LOGᶠᵇ-def Budget = StackDef.withPort≡ (FlowBudget.stack2Cat Budget)

forgetFlowBudget-def
  : ∀ {ℓ ℓRel ℓCode ℓBudgetCon ℓBudgetRel : Level}
    (Budget : ConPreorder ℓBudgetCon ℓBudgetRel)
  → FlowBudget.forget {ℓ} {ℓRel} {ℓCode} Budget
    ≡
    forgetDecorated (FlowBudget.Displayed {ℓ} {ℓRel} {ℓCode} Budget)
forgetFlowBudget-def Budget = StackDef.forget≡ (FlowBudget.stack2Cat Budget)

forgetFlow-fromProduct-def = FlowBudgetDef.forgetFlow-product

forgetBudget-fromProduct-def = FlowBudgetDef.forgetBudget-product

LOGQ-def
  : ∀ {ℓ ℓRel ℓCode ℓQ : Level}
    (Q : QAdapter ℓQ)
  → QBus.LOGQ {ℓ} {ℓRel} {ℓCode} Q
    ≡
    BudgetBus.WithPort {ℓ} {ℓRel} {ℓCode} (QBus.QBudget Q)
LOGQ-def = QBus.LOGQ≡

forgetQ-def
  : ∀ {ℓ ℓRel ℓCode ℓQ : Level}
    (Q : QAdapter ℓQ)
  → QBus.forgetQ {ℓ} {ℓRel} {ℓCode} Q
    ≡
    BudgetBus.forget {ℓ} {ℓRel} {ℓCode} (QBus.QBudget Q)
forgetQ-def = QBus.forgetQ≡

LOGQᵗ-def
  : ∀ {ℓKernelCon ℓKernelRel ℓCode ℓQ : Level}
    (Q : QAdapter ℓQ)
    (T : QClock Q)
  → QTransport.WithPort {ℓKernelCon} {ℓKernelRel} {ℓCode} {ℓQ} Q T
    ≡
    DecoratedThin2Cat (QTransport.TimeBudgetDisplayed {ℓKernelCon} {ℓKernelRel} {ℓCode} Q T)
LOGQᵗ-def Q T = SingletonDef.withPort≡ (QTransport.port2Cat Q T)

forgetTimeBudget-def
  : ∀ {ℓKernelCon ℓKernelRel ℓCode ℓQ : Level}
    (Q : QAdapter ℓQ)
    (T : QClock Q)
  → QTransport.forget {ℓKernelCon} {ℓKernelRel} {ℓCode} {ℓQ} Q T
    ≡
    forgetDecorated (QTransport.TimeBudgetDisplayed {ℓKernelCon} {ℓKernelRel} {ℓCode} Q T)
forgetTimeBudget-def Q T = SingletonDef.forget≡ (QTransport.port2Cat Q T)
