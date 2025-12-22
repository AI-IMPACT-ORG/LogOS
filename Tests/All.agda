{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.All where

-- Minimal library test aggregator:
-- typecheck the public API and the core theorem surfaces.

open import LogOS.API.Minimal
open import LogOS.Kernel
open import LogOS.Kernel.Endo

open import LogOS.Theorems.Core
open import LogOS.Theorems.Infinite
open import LogOS.Theorems.OS

-- Publication-facing packs should stay typecheckable from a single entrypoint.
import LogOS.Packs.ZFC.All as PacksZFC

-- Proof-theoretic layer (FOL + ZFC façade).
import LogOS.Logic.ZFC.All as LogicZFC

-- Kernel extension sanity checks
import Tests.Kernel.Graded

-- Coherence regression: curated public surfaces stay stable.
import Tests.CoherenceSurfaces
