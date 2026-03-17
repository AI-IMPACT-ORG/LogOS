{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Models.IterativeSetTree.CompletionAtStageSemantics where

-- Realised same-stage semantics for one chosen hierarchy stage.

open import LogOS.Prelude

import LogOS.Apps.ZFC.Stack.AsymptoticReification.CompletionSemantics as Comp

import LogOS.Apps.ZFC.Models.IterativeSetTree.CompletionAtStage as Completion
import LogOS.Apps.ZFC.Models.IterativeSetTree.HierarchyCore as Hierarchy

module For {ℓ : Level} (S : Hierarchy.StageSemanticsᵛ ℓ) where
  private
    module StageCompletion = Completion.For S

  Assumptions = StageCompletion.Assumptions
  Completion = StageCompletion.Completion
  completion = StageCompletion.completion

  module Complete (A : Completion) where
    open Comp.Complete (Hierarchy.canonicalRungᵛ S) A public
