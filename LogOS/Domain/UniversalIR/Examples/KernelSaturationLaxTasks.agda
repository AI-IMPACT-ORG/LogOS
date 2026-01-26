{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Examples.KernelSaturationLaxTasks where

-- Example: kernel closure gives a genuinely lax simulation.
--
-- Instantiate the generic “raw boundary evolution factors through Flow-saturated
-- boundary evolution” story on a concrete kernel instance (`UKR`), where:
-- - boundary order identifies codes with the same observable, and
-- - Flow is canonicalization into an explicit observable representative.

open import LogOS.Prelude

import LogOS.Computation.SchemeCategory as Cat
open import LogOS.Computation.KernelBoundaryTasks
import LogOS.Domain.Universality.KernelRich as KR

module K = ForKernel KR.UKR

-- One-step corollary: raw evolution is below the Flow-saturated evolution.
raw≤sat-step
  : ∀ c → Cat.Process._⊑_ K.SatBoundaryProcess (K.TRaw.execFrom 1 c) (K.TSat.execFrom 1 c)
raw≤sat-step c = K.execFrom≤sat 1 c

-- Task-shaped corollary: for any fuelled boundary task, the raw normal form is ≤ the saturated one.
raw≤sat-task
  : ∀ t → Cat.Process._⊑_ K.SatBoundaryProcess (K.TRaw.nfTask t) (K.TSat.nfTask t)
raw≤sat-task = K.nfTask≤sat
