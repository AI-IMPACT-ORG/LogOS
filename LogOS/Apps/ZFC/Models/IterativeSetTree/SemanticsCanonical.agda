{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Models.IterativeSetTree.SemanticsCanonical where

-- Canonical slice + bridge facades for one hierarchy section.
--
-- We keep this separate from `SemanticsStage`: many downstream users want the
-- stage assumptions and hierarchy section type without pulling the full slice
-- and bridge machinery into their import graph.

open import LogOS.Prelude using (Level)

import LogOS.Apps.ZFC.Models.IterativeSetTree.HierarchyCore as Hierarchy
import LogOS.Apps.ZFC.Models.IterativeSetTree.CanonicalBridge as CanonicalBridge
import LogOS.Apps.ZFC.Models.IterativeSetTree.CumulativeHierarchy as CumulativeHierarchy

module ForLevel (H : Hierarchy.HierarchySectionᵛ) {ℓ : Level} where
  open module Slice = CumulativeHierarchy.ForLevel H {ℓ} public using
    ( currentBase
    ; successorBase
    )

module BridgeForLevel (H : Hierarchy.HierarchySectionᵛ) {ℓ : Level} where
  open module Bridge = CanonicalBridge.ForLevel H {ℓ} public using
    ( currentBase
    ; successorBase
    ; separationSet↑
    ; replacementSet↑
    ; separation-schema↑
    ; replacement-schema↑
    )
