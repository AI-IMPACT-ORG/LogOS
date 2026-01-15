{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Complexity.Experimental.PvsNP.Public where

-- Curated P vs NP surface (experimental, publication-facing).
--
-- This module intentionally re-exports the literature-aligned interface, the
-- grade-only kernel route, and the minimal info-hardness route. The packaging-only PvsNP wrapper is kept under
-- `LogOS.Domain.Legacy.Complexity.PvsNP` (legacy aggregator: `LogOS.Domain.Legacy.All`,
-- see `docs/Legacy.md`).

import LogOS.Domain.Complexity.ClassicalPvsNP as ClassicalPvsNPₜ
module ClassicalPvsNP = ClassicalPvsNPₜ

import LogOS.Domain.Complexity.PvsNPFromInfo_Grade_Only as PvsNPFromInfo_Grade_Onlyₜ
module PvsNPFromInfo_Grade_Only = PvsNPFromInfo_Grade_Onlyₜ

-- Grade-only route (kernel-native surface).
import LogOS.Domain.Complexity.PvsNP_Grade_Only as PvsNP_Grade_Onlyₜ
module PvsNP_Grade_Only = PvsNP_Grade_Onlyₜ

-- Proof-search opacity spine (shared machinery with the GRH/opacity stack).
import LogOS.Domain.Complexity.ProofSearchOpacitySpine as ProofSearchOpacitySpineₜ
module ProofSearchOpacitySpine = ProofSearchOpacitySpineₜ
