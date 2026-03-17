{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Models.IterativeSetTree.CumulativeHierarchyCurrentCompletionSemantics where

-- Lower-rung realised completion semantics over one canonical two-rung slice.

open import LogOS.Prelude

import LogOS.Apps.ZFC.Models.IterativeSetTree.CumulativeHierarchyCompletionSemanticsAtLevel as Completion
import LogOS.Apps.ZFC.Models.IterativeSetTree.HierarchyCore as Hierarchy

module ForLevel (H : Hierarchy.HierarchySectionᵛ) {ℓ : Level} where
  module Current = Completion.ForLevelAt (λ α -> α) H {ℓ}

  Assumptions = Current.Assumptions

  CurrentCompletion : Set _
  CurrentCompletion = Current.Completion

  currentCompletion : Assumptions -> CurrentCompletion
  currentCompletion = Current.completion

  module CompleteCurrent (A : CurrentCompletion) where
    open Current.Complete A public
