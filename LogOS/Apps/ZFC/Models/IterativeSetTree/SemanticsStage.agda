{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Models.IterativeSetTree.SemanticsStage where

import LogOS.Apps.ZFC.Models.IterativeSetTree.StagedReification as Stage
import LogOS.Apps.ZFC.Models.IterativeSetTree.HierarchyCore as Hierarchy

open Stage public using
  ( Extensionalityᵛ
  ; ExtensionalCollapseᵛ
  ; PowersetStructureᵛ
  ; StageAssumptionsᵛ
  )

open Hierarchy public using (StageSemanticsᵛ; HierarchySectionᵛ)
