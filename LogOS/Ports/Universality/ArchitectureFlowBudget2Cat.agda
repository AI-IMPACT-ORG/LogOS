{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Universality.ArchitectureFlowBudget2Cat where

-- Port composition: Flow + Budget bus over the internal LOGᴳʳ basis.
--
-- This reindexes the LOG-basis flow port along `toLOG : LOGᴳʳ → LOG` and
-- composes it with the architecture-first budget bus.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder)
open import LogOS.LT.LOG.PortReindexing.Strictification using (pullbackPortEntryAlongToLOG)

import LogOS.LT.LOG.Flow2Cat as FlowLOG
import LogOS.Ports.Universality.ArchitectureBudgetBus2Cat as BudgetBusArchitecture
import LogOS.LT.Ports.PortStack.Raw as PortStack
import LogOS.LT.Ports.Template.Stack2Cat as Template

module Ports
  {ℓ ℓRel ℓCode ℓBudgetCon ℓBudgetRel : Level}
  (Budget : ConPreorder ℓBudgetCon ℓBudgetRel)
  =
  Template.BinaryEntryStackExports
    (pullbackPortEntryAlongToLOG
      (PortStack.SingletonPort.entry (FlowLOG.singleton {ℓ} {ℓRel} {ℓCode})))
    (PortStack.SingletonPort.entry
      (BudgetBusArchitecture.singleton {ℓ} {ℓRel} {ℓCode} Budget))
open Ports public using
  ( stack2Cat
  ; stack
  ; Displayed
  ; WithPort
  ; forget
  ; baseObj
  ; baseHom
  )
