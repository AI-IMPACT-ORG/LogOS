{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Models.IterativeSetTree.CumulativeHierarchy where

-- Canonical two-rung cumulative hierarchy slices for iterative set trees.
--
-- The curated entrypoint is `ForLevel`: one coherent hierarchy section plus a
-- base universe level. The canonical bridge and the same-stage completed proof
-- models are intentionally separated.

open import LogOS.Prelude

import LogOS.Apps.ZFC.Stack.AsymptoticReification.HierarchyBridgeSlice as HS

import LogOS.Apps.ZFC.Models.IterativeSetTree.HierarchyCore as Hierarchy

module ForLevel (H : Hierarchy.HierarchySectionᵛ) {ℓ : Level} where
  module Hier = Hierarchy.For H
  open module Slice = HS.For Hier.hierarchyᵛ ℓ public using
    ( currentBase
    ; successorBase
    )

  module BridgeSlice = Slice.BridgeSlice
