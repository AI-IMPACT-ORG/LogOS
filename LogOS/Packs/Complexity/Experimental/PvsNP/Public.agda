{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Complexity.Experimental.PvsNP.Public where

-- Curated P vs NP surface (experimental, publication-facing).
--
-- This module intentionally re-exports the literature-aligned interface, the
-- uniform grade-only route, the minimal info-hardness route, and the SAT target.

import LogOS.Domain.Complexity.PvsNPLedger as PvsNPLedger

import LogOS.Domain.Complexity.PvsNPFromInfo_Grade_Only as PvsNPFromInfo_Grade_Only

-- Grade-only route (kernel-native surface).
import LogOS.Domain.Complexity.PvsNP_Grade_Only as PvsNP_Grade_Only

-- Proof-search opacity spine (shared machinery with the GRH/opacity stack).
import LogOS.Domain.Complexity.ProofSearchOpacitySpine as ProofSearchOpacitySpine

-- SAT targets (canonical NP-complete front door).
import LogOS.Domain.Complexity.Targets.SAT as SAT

import LogOS.Domain.Complexity.Targets.SATProofSearch as SATProofSearch
