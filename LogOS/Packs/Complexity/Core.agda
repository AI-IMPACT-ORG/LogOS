{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Complexity.Core where

-- Curated, stable complexity surface (no demos).
-- For a minimal P/NP-only public surface, prefer LogOS.Packs.Complexity.PvsNP.Public.
--
-- This is the most convenient import if you want the complexity-facing API
-- (including the verification-vs-search centerpiece) without pulling in every
-- internal module under `Domain/Complexity/*`.

open import LogOS.Domain.Complexity.ProofSearchSeparation public

-- Grade-only route.
import LogOS.Domain.Complexity.PvsNP_Grade_Only as PvsNP_Grade_Onlyₜ
module PvsNP_Grade_Only = PvsNP_Grade_Onlyₜ

-- Avoid `For` name clashes: re-export the classical surface under its own namespace.
import LogOS.Domain.Complexity.ClassicalPvsNP as ClassicalPvsNPₜ
module ClassicalPvsNP = ClassicalPvsNPₜ

-- Info-hardness route (minimal physical axioms).
import LogOS.Domain.Complexity.PvsNPFromInfo_Grade_Only as PvsNPFromInfo_Grade_Onlyₜ
module PvsNPFromInfo_Grade_Only = PvsNPFromInfo_Grade_Onlyₜ
