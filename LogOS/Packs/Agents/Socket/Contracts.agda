{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Socket.Contracts where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Free.ConstraintsOverSig using (Con∂)

-- Functorial contracts: written in the signature-indexed free language `Con∂`.
--
-- These are *syntax* (not semantics): interpretation into a particular kernel’s
-- boundary constraints is supplied separately by a valuation of atomic ports.

record AgentContracts {ℓ : Level} (Sig : LogOSSignature ℓ) : Set (lsuc ℓ) where
  field
    Objective : Con∂ Sig
    Safety    : Con∂ Sig
    Assumes   : Con∂ Sig

open AgentContracts public

