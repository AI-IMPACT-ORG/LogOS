{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Laws.FiniteKernel.Adapters where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Truth as Truth
open import LogOS.Minimal.Con
open import LogOS.Kernel
open import LogOS.Kernel.Hom
-- (Guarded code/truth theorems are not re-exported here)

-- Adapter-level theorems and helpers.
--
-- This module provides general imports and keeps adapter
-- results that do not require constructing a specific initial kernel. The
-- initial-kernel builders and fold homomorphisms are in `LogOS.Kernel.Initial`.
-- Guarded γ* preservation theorems are exposed via `LogOS.Theorems.Boundary.Guarded`.
