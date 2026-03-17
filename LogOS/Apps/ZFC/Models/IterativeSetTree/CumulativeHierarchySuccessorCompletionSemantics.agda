{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Models.IterativeSetTree.CumulativeHierarchySuccessorCompletionSemantics where

-- Successor-rung realised completion semantics over one canonical two-rung slice.

open import LogOS.Prelude

import LogOS.Apps.ZFC.Models.IterativeSetTree.CumulativeHierarchyCompletionSemanticsAtLevel as Completion
import LogOS.Apps.ZFC.Models.IterativeSetTree.HierarchyCore as Hierarchy

module ForLevel (H : Hierarchy.HierarchySectionᵛ) {ℓ : Level} where
  module Successor = Completion.ForLevelAt lsuc H {ℓ}

  Assumptions = Successor.Assumptions

  SuccessorCompletion : Set _
  SuccessorCompletion = Successor.Completion

  successorCompletion : Assumptions -> SuccessorCompletion
  successorCompletion = Successor.completion

  module CompleteSuccessor (A : SuccessorCompletion) where
    open Successor.Complete A public
