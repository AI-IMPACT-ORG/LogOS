{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Models.IterativeSetTree.CompletionAtStage where

-- Same-stage completion at one fixed rung.
--
-- This is the mathematically primitive completion surface: choose one stage,
-- derive the late-collapse assumptions for that stage, and build the local
-- completion witness for exactly that rung.

open import LogOS.Prelude

import LogOS.Apps.ZFC.Stack.AsymptoticReification.CompletionWitness as Witness

import LogOS.Apps.ZFC.Models.IterativeSetTree.HierarchyCompletion as HierarchyCompletion
import LogOS.Apps.ZFC.Models.IterativeSetTree.HierarchyCore as Hierarchy
import LogOS.Apps.ZFC.Models.IterativeSetTree.LateCollapseAssumptions as LC
import LogOS.Apps.ZFC.Models.IterativeSetTree.StagedReification as Stage

module For {ℓ : Level} (S : Hierarchy.StageSemanticsᵛ ℓ) where
  private
    stage : Stage.StageAssumptionsᵛ {ℓ}
    stage = Hierarchy.assumptionsᵛ S

    rung = Hierarchy.canonicalRungᵛ S

  module Collapse = LC.For stage

  Assumptions = Collapse.Assumptions

  Completion : Set _
  Completion = Witness.CompletionWitness rung

  completion : Assumptions -> Completion
  completion A =
    HierarchyCompletion.completionWitnessForStageᵛ
      S
      (Collapse.completionWitnessᵛ A)
