{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.AsymptoticReification.HierarchySlice where

-- Slice one successor step out of a coherent hierarchy object.
--
-- This module makes the crucial distinction explicit in the type shape:
-- - the cross-stage bridge is canonical once the hierarchy is fixed,
-- - same-stage proof models still require local completion data at the rung.

open import LogOS.Prelude
open import LogOS.LT.Stage.SuccessorChain using (SuccessorChain)

import LogOS.Apps.ZFC.Stack.AsymptoticReification.CompletionLayer as Comp
import LogOS.Apps.ZFC.Stack.AsymptoticReification.HierarchyBridgeSlice as HS
import LogOS.Apps.ZFC.Stack.AsymptoticReification.SuccessorHierarchy as Hier

module For {ℓStage : Level} {Stage : Set ℓStage} {Chain : SuccessorChain Stage}
  (H : Hier.SuccessorHierarchy Chain)
  (i : Stage)
  where

  open SuccessorChain Chain using (next)
  open Hier.SuccessorHierarchy H using (ctxLevel; rungAt)

  private
    i↑ : Stage
    i↑ = next i

  module Slice = HS.For H i

  currentBase = Slice.currentBase
  successorBase = Slice.successorBase

  module BridgeSlice = Slice.BridgeSlice

  LocalCompletion : (j : Stage) -> Set (lsuc (lsuc (ctxLevel j)))
  LocalCompletion j = Comp.CompletionLayer (rungAt j)

  CurrentCompletion : Set (lsuc (lsuc (ctxLevel i)))
  CurrentCompletion = LocalCompletion i

  SuccessorCompletion : Set (lsuc (lsuc (ctxLevel i↑)))
  SuccessorCompletion = LocalCompletion i↑

  module CompleteAt (j : Stage) (A : LocalCompletion j) where
    open Comp.CompletionLayer A public

  module CompleteCurrent (A : CurrentCompletion) = CompleteAt i A
  module CompleteSuccessor (A : SuccessorCompletion) = CompleteAt i↑ A

  module CompleteBoth (A₀ : CurrentCompletion) (A₁ : SuccessorCompletion) where
    module Current = CompleteCurrent A₀
    module Successor = CompleteSuccessor A₁
