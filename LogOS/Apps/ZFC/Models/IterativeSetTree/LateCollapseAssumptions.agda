{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Models.IterativeSetTree.LateCollapseAssumptions where

-- Same-stage completion assumptions for one iterative-tree rung.
--
-- This module packages only the witness data required to complete the canonical
-- rung. Realised same-stage semantics live in `LateCollapseSemantics`.

open import LogOS.Prelude

import LogOS.Apps.ZFC.Stack.AsymptoticReification.CanonicalRung as ZR
import LogOS.Apps.ZFC.Stack.AsymptoticReification.CompletionWitness as Witness
import LogOS.Apps.ZFC.Stack.ProfileTower.Core as Tower
import LogOS.Apps.ZFC.Stack.WellFounded as WFd

import LogOS.Apps.ZFC.Models.IterativeSetTree.HierarchyCore as Hier
import LogOS.Apps.ZFC.Models.IterativeSetTree.HierarchyInfinity as Inf
import LogOS.Apps.ZFC.Models.IterativeSetTree.RankBoundedFO as TreeFO
import LogOS.Apps.ZFC.Models.IterativeSetTree.StageSetup as Setup
import LogOS.Apps.ZFC.Models.IterativeSetTree.StagedReification as Stage
import LogOS.Apps.ZFC.Models.IterativeSetTree.WellFounded as Wf

module For {ℓ : Level} (H : Stage.StageAssumptionsᵛ {ℓ}) where
  module Setupᵛ = Setup.For H
  open Setupᵛ using (C; collapseFlowStagedᵛ)
  module Infinity = Inf.For H
  module TreeFOᵛ = TreeFO.For H
  module LC = Setupᵛ.LCStaged

  module Collapse = LC.WithFlowCollapse collapseFlowStagedᵛ
  module Bundle = Collapse.ForBase Infinity.baseAssumptions
  module FO = TreeFOᵛ.ForBase Infinity.baseAssumptions

  canonicalRungᵛ : ZR.CanonicalRung C
  canonicalRungᵛ = Hier.canonicalRungFromAssumptionsᵛ H

  base : Tower.ZFStackBase {lsuc ℓ}
  base = Bundle.base

  record Assumptions : Set (lsuc (lsuc (lsuc ℓ))) where
    field
      foRepresentability : FO.FORepresentabilityᵛ
      structural : Bundle.StructuralAssumptions

  foWitnessesᵛ : Assumptions → Bundle.FO.StagedFOWitnesses
  foWitnessesᵛ A = FO.stagedFOWitnesses (Assumptions.foRepresentability A)

  wfMemᵛ : (x : Tower.ZFStackBase.SetU base) → WFd.Acc (Tower.ZFStackBase._∈_ base) x
  wfMemᵛ = Wf.wfCtxᵛ

  structuralAssumptionsᵛ : Assumptions → Bundle.StructuralAssumptions
  structuralAssumptionsᵛ = Assumptions.structural

  Completion : Set _
  Completion = Witness.CompletionWitness canonicalRungᵛ

  completionWitnessᵛ : Assumptions -> Completion
  completionWitnessᵛ A =
    record
      { foWitnesses = foWitnessesᵛ A
      ; wfMem = wfMemᵛ
      ; structural = structuralAssumptionsᵛ A
      }
