{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Universality.ArchitectureBudgetBus2Cat where

-- Budget bus over the internal LOGᴳʳ basis (strict pullback along `toLOG : LOGᴳʳ → LOG`).

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder)

import LogOS.Ports.Universality.BudgetBus2Cat as BudgetLOG
import LogOS.LT.LOG.PortReindexing.Strictification as PortReindexing

open BudgetLOG public using (BudgetTag; budgetTag)

module Port {ℓ ℓRel ℓCode ℓBudgetCon ℓBudgetRel : Level}
  (Budget : ConPreorder ℓBudgetCon ℓBudgetRel)
  = PortReindexing.PullbackSingletonExportsAlongToLOG
      (BudgetLOG.budgetSig {ℓ} {ℓRel} {ℓCode} Budget)

open Port public using
  ( port2Cat
  ; singleton
  ; stack
  ; port
  ; Displayed
  ; WithPort
  ; forget
  )
