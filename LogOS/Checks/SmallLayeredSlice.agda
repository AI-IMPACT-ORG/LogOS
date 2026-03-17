{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.SmallLayeredSlice where

-- Minimal executable template for the “one observation layer + one telemetry
-- layer + one witness” downstream pattern.

open import LogOS.Prelude

import LogOS.Apps.Physics.MeasurementExample as Physics

observationLayer = Physics.observationLayer

telemetryLayer = Physics.telemetryLayer

adequacyWitness = Physics.OutcomeIdentityAdequacy

coarseRefinesFine = Physics.coarse-refines-fine
