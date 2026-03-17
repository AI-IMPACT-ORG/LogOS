{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Models.IterativeSetTree.CumulativeHierarchyCompletion where

-- Optional same-stage completion surfaces over a canonical two-rung slice.
--
-- The current and successor completion layers are kept separate here: this
-- preserves the canonical/bridge/completion split while avoiding a combined
-- wrapper that re-instantiates both late-collapse layers in one interface.
import LogOS.Apps.ZFC.Models.IterativeSetTree.CumulativeHierarchyCurrentCompletion
import LogOS.Apps.ZFC.Models.IterativeSetTree.CumulativeHierarchySuccessorCompletion

module CurrentForLevel = LogOS.Apps.ZFC.Models.IterativeSetTree.CumulativeHierarchyCurrentCompletion.ForLevel
module SuccessorForLevel = LogOS.Apps.ZFC.Models.IterativeSetTree.CumulativeHierarchySuccessorCompletion.ForLevel
