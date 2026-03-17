{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Models.IterativeSetTree.Hierarchy where

-- Compatibility facade for the iterative-tree hierarchy surface.
--
-- The canonical hierarchy data now live in `HierarchyCore`, and completion
-- witness transport lives in `HierarchyCompletion`. This module keeps the old
-- import path while re-exporting the split structure.

open import LogOS.Prelude

import LogOS.Apps.ZFC.Models.IterativeSetTree.HierarchyCompletion as Completion
import LogOS.Apps.ZFC.Models.IterativeSetTree.HierarchyCore as Core

open Core public using
  ( canonicalRungFromAssumptionsᵛ
  ; StageSemanticsᵛ
  ; mkStageSemanticsᵛ
  ; assumptionsᵛ
  ; canonicalRungᵛ
  ; HierarchySectionᵛ
  )
open Completion public using (completionWitnessForStageᵛ)

module For (H : HierarchySectionᵛ) where
  open Core.For H public using (hierarchyᵛ)
