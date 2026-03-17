{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.UniversalityAdapterTemplate where

-- Minimal executable template for the “define one canonical `FuelAdapter`,
-- then read off the deck-level consequences” pattern.

open import LogOS.Prelude

import LogOS.Ports.Universality.Task as Task
import LogOS.Ports.Universality.Core as Core
import LogOS.Adapters.Universality.Minsky as Minsky
import LogOS.Apps.Universality.Stack as Stack
import LogOS.Apps.Universality.Architecture as Architecture
import LogOS.Apps.Universality.Agreement.Task as TaskAgreement

adapter = Minsky.minskyFuelAdapter

adapterKernel = Core.mkFuelKernel adapter

adapterKernelHom = Core.fuelKernelHom adapter

adapterDeckEntry = Stack.fromMinsky

allAdapters = Stack.allAdapters

sampleTask : Task.PATask
sampleTask = Task.addTask 1 2

sampleMeasuredAgreement =
  Architecture.adapterMeasuredAgreement
    TaskAgreement.taskEncodings
