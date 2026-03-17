{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.Universality.Architecture where

-- Flagship app-side façade for the universality stack.
--
-- The same adapter stack drives:
-- - the universal kernel map,
-- - the CTD ledger,
-- - the measured-agreement family,
-- - the observational `Flow + Budget` stack on `LOG`,
-- - the architecture-first `Flow + Budget` stack on `LOGᴳʳ`.
--
-- Practical usage rule:
-- stay on this surface unless you are extending the lower-rung adapter or
-- stack machinery itself.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder)
open import LogOS.LT.LOG.Kernel2Cat using (LOG)
open import LogOS.LT.LOG.Implementation2Cat.Core using (LOGᴳʳ)
open import LogOS.Ports.CriticalParameter using (CriticalCut)

import LogOS.LT.Ports.Template.Stack2Cat as Template
import LogOS.Ports.Universality.Core as Core
import LogOS.Ports.Universality.FlowBudget2Cat as FlowBudget2Cat
import LogOS.Ports.Universality.ArchitectureFlowBudget2Cat as ArchitectureFlowBudget2Cat

import LogOS.Apps.Universality.Stack as Stack
open Stack public using
  ( UniversalityAdapter
  ; UniversalityAdapterCode
  ; AdapterDescriptor
  ; allAdapters
  ; adapterDescriptor
  ; adapterFuelBoundary
  ; adapterFuel
  ; adapterObservation
  ; adapterKernel
  ; adapterKernelHom
  )
import LogOS.Apps.Universality.CTD as CTD
open CTD public using
  ( ctdLedger
  )
  renaming
  ( simulate to adapterLedger
  )
import LogOS.Apps.Universality.Agreement.Universal as Universal
open Universal public using
  ( MeasuredEncodings
  ; ParadigmsAgreement
  )
  renaming
  ( measuredParadigmsAgreement to adapterMeasuredAgreement
  )

observationalFlowBudgetStack
  : ∀ {ℓ ℓRel ℓCode ℓBudgetCon ℓBudgetRel : Level}
  → (Budget : ConPreorder ℓBudgetCon ℓBudgetRel)
  → Template.Stack2Cat (LOG {ℓ} {ℓRel} {ℓCode})
observationalFlowBudgetStack = FlowBudget2Cat.stack2Cat

architecturalFlowBudgetStack
  : ∀ {ℓ ℓRel ℓCode ℓBudgetCon ℓBudgetRel : Level}
  → (Budget : ConPreorder ℓBudgetCon ℓBudgetRel)
  → Template.Stack2Cat (LOGᴳʳ {ℓ} {ℓRel} {ℓCode})
architecturalFlowBudgetStack = ArchitectureFlowBudget2Cat.stack2Cat

adapterBudgetCutFamily
  : (a : Stack.UniversalityAdapter)
  → (γ : Stack.UniversalityAdapterCode a)
  → CriticalCut
      Core.universalBoundary
      (λ budget → Core.BudgetEnough (Stack.adapterCodeBoundary a γ) budget)
adapterBudgetCutFamily = Stack.adapterCriticalBudget
