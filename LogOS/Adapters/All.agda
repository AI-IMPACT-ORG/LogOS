{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Adapters.All where

-- Lean re-exports of adapter-level theorems (model morphisms, initial → target)

open import LogOS.Theorems.Laws.FiniteKernel.H public  -- fold preservation and completeness
open import LogOS.Theorems.Boundary.Mu public  -- μ-unfold and induction
open import LogOS.Theorems.Boundary.Guarded public  -- guarded γ* preservation and reflection laws
open import LogOS.Theorems.Boundary.Continuity public  -- Scott continuity wrappers
open import LogOS.Theorems.Laws.FiniteKernel.Adapters public  -- initial → target adapter helpers
