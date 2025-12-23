{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Models.Complexity.PvsNP.Public where

-- Curated P vs NP surface (safe, publication-facing).
--
-- This module intentionally re-exports only the PvsNP and
-- literature-aligned interfaces plus the minimal info-hardness route.
-- It excludes the grade-only P/NP-shaped pack to reduce misreadings.
-- Note: `PvsNP` is a packaging layer; its `Assumptions` already include `InNP` + `¬ InP`.

import LogOS.Domain.Complexity.PvsNP as PvsNPₜ
module PvsNP = PvsNPₜ

import LogOS.Domain.Complexity.ClassicalPvsNP as ClassicalPvsNPₜ
module ClassicalPvsNP = ClassicalPvsNPₜ

import LogOS.Domain.Complexity.PvsNPFromInfo_Grade_Only as PvsNPFromInfo_Grade_Onlyₜ
module PvsNPFromInfo_Grade_Only = PvsNPFromInfo_Grade_Onlyₜ

-- Proof-search opacity spine (shared machinery with the GRH/opacity stack).
import LogOS.Domain.Complexity.ProofSearchOpacitySpine as ProofSearchOpacitySpineₜ
module ProofSearchOpacitySpine = ProofSearchOpacitySpineₜ
