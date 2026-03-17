{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.AsymptoticReification.HierarchyBridgeSlice where

-- Canonical one-step slice of a successor hierarchy.
--
-- This module contains only the data determined canonically by the hierarchy:
-- the current rung, the successor rung, and the cross-stage bridge between
-- them. Local completion witnesses are intentionally excluded.

open import LogOS.Prelude
open import LogOS.LT.Stage.SuccessorChain using (SuccessorChain)

import LogOS.Apps.ZFC.Stack.AsymptoticReification.CanonicalRung as Canonical
import LogOS.Apps.ZFC.Stack.AsymptoticReification.SuccessorBridge as Bridge
import LogOS.Apps.ZFC.Stack.AsymptoticReification.SuccessorHierarchy as Hier

module For {ℓStage : Level} {Stage : Set ℓStage} {Chain : SuccessorChain Stage}
  (H : Hier.SuccessorHierarchy Chain)
  (i : Stage)
  where

  open SuccessorChain Chain using (next)
  open Hier.SuccessorHierarchy H

  private
    i↑ : Stage
    i↑ = next i

    K₀ : Canonical.CanonicalRung (ctxAt i)
    K₀ = rungAt i

    K₁ : Canonical.CanonicalRung (ctxAt i↑)
    K₁ = rungAt i↑

    B↑ : SuccessorBridgeAt i
    B↑ = successorBridge i

    module R₀ = Canonical.CanonicalRung K₀
    module R₁ = Canonical.CanonicalRung K₁

  currentBase = R₀.base
  successorBase = R₁.base

  module BridgeSlice = Bridge.SuccessorBridge B↑
