{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Boundary.Stabilisation where

-- Curated “stabilisation kit”:
-- μ / Kleene iteration + continuity packaging + μ-fusion transport.
--
-- This module is intentionally *narrower* than `LogOS.Theorems.Boundary.All`:
-- it collects only the domain-theoretic glue used to talk about stabilized
-- truth/closures and their transport.

open import LogOS.Prelude

import LogOS.Theorems.Boundary.Mu as Muₜ
import LogOS.Theorems.Boundary.ContinuityCore as ContinuityCoreₜ
import LogOS.Theorems.Boundary.Continuity as Continuityₜ
import LogOS.Theorems.Boundary.MuFusion as MuFusionₜ
import LogOS.Theorems.Boundary.OmegaCPOMapKit as OmegaCPOMapKitₜ

module Mu = Muₜ
module ContinuityCore = ContinuityCoreₜ
module Continuity = Continuityₜ
module MuFusion = MuFusionₜ
module OmegaCPOMapKit = OmegaCPOMapKitₜ
