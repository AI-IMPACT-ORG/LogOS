{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Models.IterativeSetTree.CumulativeHierarchyCompletionSemanticsAtLevel where

-- Hierarchy-level selector helper for realised same-stage completion semantics.

open import LogOS.Prelude
open import LogOS.LT.Stage.Section as Sec using (at)

import LogOS.Apps.ZFC.Models.IterativeSetTree.CompletionAtStageSemantics as Completion
import LogOS.Apps.ZFC.Models.IterativeSetTree.HierarchyCore as Hierarchy

module ForLevelAt (next : Level -> Level)
  (H : Hierarchy.HierarchySectionᵛ)
  {ℓ : Level}
  where
  private
    selectedStage : Hierarchy.StageSemanticsᵛ (next ℓ)
    selectedStage = at H (next ℓ)

  module Selected = Completion.For selectedStage

  Assumptions = Selected.Assumptions

  Completion : Set _
  Completion = Selected.Completion

  completion : Assumptions -> Completion
  completion = Selected.completion

  module Complete (A : Completion) where
    open Selected.Complete A public
