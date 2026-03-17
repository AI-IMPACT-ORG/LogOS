{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.Universality.All where

-- Universality pack (v1.1).
--
-- Goal: package a flagship stacked-transformer universality architecture:
-- - one adapter deck
-- - one universal kernel/CTD ledger
-- - one measured agreement family
-- - one observational and one architecture-first `Flow + Budget` stack view
--
-- Entrypoints:
-- - `LogOS/Apps/Universality/Architecture.agda`
-- - `LogOS/Apps/Universality/Stack.agda`
-- - `LogOS/Apps/Universality/CTD.agda`
-- - `LogOS/Apps/Universality/Agreement.agda`
-- - `LogOS/Ports/Universality/Core.agda`
-- - `LogOS/Ports/Universality/Task.agda`
-- - adapters: `LogOS/Adapters/Universality/*`
-- - executable templates:
--   `LogOS/Checks/UniversalityArchitecture.agda`
--   `LogOS/Checks/UniversalityAdapterTemplate.agda`
-- - guide: `docs/Interpretations/Applications/Application_Sketches.lagda.md`
--
-- Implemented now:
-- - the implemented surfaces are exactly the imports below
-- - detailed application narration lives in
--   `docs/Interpretations/Applications/Application_Sketches.lagda.md`
--
-- Planned:
-- - roadmap and next-step tracking live in external project planning docs
--
-- Governance rule (design bubble control):
-- - if a relation is not induced by a named port or view, treat it as a design bubble and refactor first

import LogOS.Ports.Universality.Core as Core
import LogOS.Ports.Universality.Task as Task

import LogOS.Adapters.Universality.Minsky as Minsky
import LogOS.Adapters.Universality.Lambda as Lambda
import LogOS.Adapters.Universality.EVM as EVM
import LogOS.Adapters.Universality.PreQuantum as PreQuantum
import LogOS.Adapters.Universality.PreQuantumCircuit as PreQuantumCircuit

import LogOS.Apps.Universality.Architecture as Architecture
import LogOS.Apps.Universality.Stack as Stack
import LogOS.Apps.Universality.CTD as CTD
import LogOS.Apps.Universality.Agreement as Agreement
