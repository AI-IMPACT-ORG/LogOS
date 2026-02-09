{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.UniversalIR.Guardrails where

-- Optional “guardrails” surface for the UniversalIR storyline:
-- representation invariance, functoriality, and diagonal/budget barrier results.
--
-- This module is intentionally *not* re-exported from the stable
-- `LogOS.Packs.UniversalIR.All` umbrella to keep stable surfaces free of
-- diagonalisation assumption dependencies.

import LogOS.Computation.SchemeCategory as SchemeCategoryₜ
import LogOS.Computation.Scheme as Schemeₜ
import LogOS.Theorems.Meta.SpectralSeparationOutput as SpectralSeparationOutputₜ
import LogOS.Theorems.Meta.Tarski as Tarskiₜ
import LogOS.Theorems.Meta.Assumptions.Diagonal as Diagonalₜ
import LogOS.Theorems.Meta.BudgetedSeparationOutput as BudgetedSeparationOutputₜ

module SchemeCategory = SchemeCategoryₜ
module Scheme = Schemeₜ
module SpectralSeparationOutput = SpectralSeparationOutputₜ
module Tarski = Tarskiₜ
module Diagonal = Diagonalₜ
module BudgetedSeparationOutput = BudgetedSeparationOutputₜ

