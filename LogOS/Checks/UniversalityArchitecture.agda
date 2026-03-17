{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.UniversalityArchitecture where

open import LogOS.Prelude
open import LogOS.LT.LOG.Kernel2Cat using (LOG)
open import LogOS.LT.LOG.Implementation2Cat.Core using (LOGᴳʳ)

import LogOS.LT.Ports.Template.Stack2Cat as Template
import LogOS.Ports.Universality.Core as Core
import LogOS.Ports.Universality.Task as Task
import LogOS.Adapters.Universality.Minsky as Minsky
import LogOS.Apps.Universality.Stack as Stack
import LogOS.Apps.Universality.CTD as CTD
import LogOS.Apps.Universality.Architecture as Architecture
import LogOS.Apps.Universality.Agreement.Task as TaskAgreement
import LogOS.Apps.Universality.Agreement.ExprTask as ExprTaskAgreement

allAdapters = Stack.allAdapters

singleAdapterValue = Minsky.minskyFuelAdapter

singleAdapterKernel = Core.mkFuelKernel singleAdapterValue

singleAdapterKernelHom = Core.fuelKernelHom singleAdapterValue

singleAdapterDeckEntry = Stack.fromMinsky

taskAgreement =
  TaskAgreement.taskParadigmsAgreement

exprTaskAgreement =
  ExprTaskAgreement.exprTaskParadigmsAgreement

sampleTask : Task.PATask
sampleTask = Task.addTask 2 3

sampleCriticalCut =
  Architecture.adapterBudgetCutFamily
    Stack.fromMinsky
    (Minsky.minskyFromPATask sampleTask)

sampleMeasuredAgreement =
  Architecture.adapterMeasuredAgreement
    TaskAgreement.taskEncodings

observationalStack
  : Template.Stack2Cat (LOG {lzero} {lzero} {lzero})
observationalStack =
  Architecture.observationalFlowBudgetStack Core.universalBoundary

architecturalStack
  : Template.Stack2Cat (LOGᴳʳ {lzero} {lzero} {lzero})
architecturalStack =
  Architecture.architecturalFlowBudgetStack Core.universalBoundary

ctdLedger = CTD.ctdLedger
