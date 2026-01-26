{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.InfoTheory.Applications.ThermoRG where

import LogOS.Domain.InfoTheory.Shannon.ThermoRG as ThermoRGₜ

-- Math-facing definitions live under `For` (parameterized by `ShannonFacts`).
module For = ThermoRGₜ.For

-- Standard quartet wrapper (uniform API).
module Quartet = ThermoRGₜ.QuartetThermoRG
open Quartet public using (Assumptions; Claim; Pack; mkPack; assumptionsOf; claimOf)
