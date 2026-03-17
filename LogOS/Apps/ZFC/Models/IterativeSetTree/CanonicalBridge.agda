{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Models.IterativeSetTree.CanonicalBridge where

-- Tiny iterative-tree instantiation of the generic theorem-facing successor
-- bridge names.
--
-- This module deliberately stays bridge-only: it exposes the canonical
-- successor-stage Separation/Replacement sets and their membership theorems,
-- but it does not import same-stage completion machinery.

open import LogOS.Prelude

import LogOS.Apps.ZFC.Models.IterativeSetTree.CumulativeHierarchy as CH
import LogOS.Apps.ZFC.Models.IterativeSetTree.HierarchyCore as Hierarchy

module ForLevel (H : Hierarchy.HierarchySectionᵛ) {ℓ : Level} where
  module Slice = CH.ForLevel H {ℓ}
  module Bridge = Slice.BridgeSlice

  open Slice public using
    ( currentBase
    ; successorBase
    )

  open Bridge public using
    ( separationSet↑
    ; replacementSet↑
    ; separation-schema↑
    ; replacement-schema↑
    )
