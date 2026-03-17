{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Models.IterativeSetTree.HierarchyCompletion where

-- Completion-witness transport over the canonical iterative-tree hierarchy core.

open import LogOS.Prelude

import LogOS.Apps.ZFC.Stack.AsymptoticReification.CompletionWitness as Witness
import LogOS.Apps.ZFC.Models.IterativeSetTree.HierarchyCore as Core

completionWitnessForStageᵛ
  : ∀ {ℓ : Level}
  -> (S : Core.StageSemanticsᵛ ℓ)
  -> Witness.CompletionWitness (Core.canonicalRungFromAssumptionsᵛ (Core.assumptionsᵛ S))
  -> Witness.CompletionWitness (Core.canonicalRungᵛ S)
completionWitnessForStageᵛ S A rewrite Core.StageSemanticsᵛ.canonicalRung-okᵛ S = A
