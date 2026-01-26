{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Frameworks.MetaReasoning where

open import LogOS.Prelude

-- Meta-reasoning / bounded rationality: reuse the existing modal/meta theorem
-- surfaces (Löb/Gödel) and the budgeted observer barriers.

open import LogOS.Theorems.Meta.Lob public
open import LogOS.Theorems.Meta.SpectralSeparationOutput public
open import LogOS.Theorems.Meta.Tarski public using (undef-classical)
open import LogOS.Theorems.Meta.Assumptions.Diagonal public using (noOmniscientDeciderC)
open import LogOS.Theorems.Meta.BudgetedSeparationOutput public
