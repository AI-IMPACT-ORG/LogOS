{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.InfoTheory.Applications.DPI where

import LogOS.Domain.InfoTheory.Shannon.DPI as DPIₜ

-- Math-facing definitions live under `For` (parameterized by `ShannonFacts`).
module For = DPIₜ.For

-- Axiom pack for the DPI route.
open DPIₜ public using (DPIFacts)

-- Standard quartet wrapper (uniform API).
module Quartet = DPIₜ.QuartetDPI
open Quartet public using (Assumptions; Claim; Pack; mkPack; assumptionsOf; claimOf)
