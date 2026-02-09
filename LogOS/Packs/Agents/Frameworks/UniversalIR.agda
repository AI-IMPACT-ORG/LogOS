{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Frameworks.UniversalIR where

open import LogOS.Prelude

-- UniversalIR is already expressed in “agent framework” form:
-- a shared `Process` (`UProcess`) plus many `Interface` instances (compiler + fuel)
-- for different paradigms (Minsky, λ-calculus, EVM, quantum oracle/circuits).
--
-- This module re-exports those ready-made choices so they can be plugged into an
-- `AgentSocket` without additional scaffolding.
--
-- We import via the curated pack surface so this stays stable even if the
-- internal Domain layout evolves.

import LogOS.Packs.UniversalIR.Core as UIRCore
open UIRCore.Task public using (PATask)
open UIRCore.Schemes public
  using
    ( UProcess
    ; minskyInterface
    ; lambdaInterface
    ; ethereumInterface
    ; oracleInterface
    ; quantumCircuitInterface
    ; minskyScheme
    ; lambdaScheme
    ; ethereumScheme
    ; oracleScheme
    ; quantumCircuitScheme
    )
