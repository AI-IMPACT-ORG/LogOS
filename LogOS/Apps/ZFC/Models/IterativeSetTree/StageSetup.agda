{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Models.IterativeSetTree.StageSetup where

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (refl⊑)

import LogOS.Apps.ZFC.Stack.AsymptoticReification as AR
import LogOS.Apps.ZFC.Stack.AsymptoticReification.LateCollapseTower as LCT
import LogOS.Apps.ZFC.Stack.ZFCore as ZF

import LogOS.Apps.ZFC.Models.IterativeSetTree.Context as Ctx
import LogOS.Apps.ZFC.Models.IterativeSetTree.StagedReification as Stage

-- Shared setup for iterative-set-tree modules that start from staged
-- admissibility data and immediately derive the restricted refinement surface.
module For {ℓ : Level} (H : Stage.StageAssumptionsᵛ {ℓ}) where
  open Stage.StageAssumptionsᵛ H public using (collapse)

  C : ZF.SetContext {lsuc ℓ}
  C = Ctx.ctxᵛ {ℓ}

  module Stageᵛ = Stage.For H

  stagedPredicateReificationᵛ : AR.StagedPredicateReification C
  stagedPredicateReificationᵛ = Stageᵛ.stagedPredicateReificationᵛ

  restrictedPredicateReificationᵛ : AR.PredicateReification C
  restrictedPredicateReificationᵛ = AR.staged→restricted stagedPredicateReificationᵛ

  module R = AR.PredicateReification restrictedPredicateReificationᵛ

  module LC = LCT.For C restrictedPredicateReificationᵛ

  collapseFlowᵛ : LC.FlowCollapse
  collapseFlowᵛ _ = refl⊑ R.PredBnd

  module LCStaged = LCT.ForStaged C stagedPredicateReificationᵛ

  collapseFlowStagedᵛ : LCStaged.FlowCollapse
  collapseFlowStagedᵛ _ = refl⊑ R.PredBnd
