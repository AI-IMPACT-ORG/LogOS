{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Complexity.Experimental.Core where

-- Curated, experimental complexity surface (no demos).
-- For a minimal P/NP-only public surface, prefer
-- LogOS.Packs.Complexity.Experimental.PvsNP.Public.
--
-- This is the most convenient import if you want the complexity-facing API
-- (including the verification-vs-search centerpiece) without pulling in every
-- internal module under `Domain/Complexity/*`.

open import LogOS.Packs.Trust using (PackTrust; experimental)

packTrust : PackTrust
packTrust = record { level = experimental }

open import LogOS.Domain.Complexity.ProofSearchSeparation public
open import LogOS.Domain.Complexity.Reduction public

-- Grade-only route.
import LogOS.Domain.Complexity.PvsNP_Grade_Only as PvsNP_Grade_Onlyₜ
module PvsNP_Grade_Only = PvsNP_Grade_Onlyₜ

-- Avoid `For` name clashes: re-export the P/NP ledger under its own namespace.
import LogOS.Domain.Complexity.PvsNPLedger as PvsNPLedgerₜ
module PvsNPLedger = PvsNPLedgerₜ

-- Info-hardness route (minimal physical axioms).
import LogOS.Domain.Complexity.PvsNPFromInfo_Grade_Only as PvsNPFromInfo_Grade_Onlyₜ
module PvsNPFromInfo_Grade_Only = PvsNPFromInfo_Grade_Onlyₜ
