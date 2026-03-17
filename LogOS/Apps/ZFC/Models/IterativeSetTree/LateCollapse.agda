{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Models.IterativeSetTree.LateCollapse where

-- Compatibility facade for iterative-tree same-stage completion.
--
-- Witness data now live in `LateCollapseAssumptions`, and realised same-stage
-- semantics live in `LateCollapseSemantics`. This module keeps the old import
-- path while exposing the former bundled surface.

open import LogOS.Prelude

import LogOS.Apps.ZFC.Stack.AsymptoticReification.CompletionLayer as Comp
import LogOS.Apps.ZFC.Proof.Semantics.Core as SemCore
import LogOS.Apps.ZFC.Stack.ProfileTower.Core as Tower
import LogOS.Apps.ZFC.Stack.ProfileTowerFO as TowerFO

import LogOS.Apps.ZFC.Models.IterativeSetTree.LateCollapseAssumptions as Witnesses
import LogOS.Apps.ZFC.Models.IterativeSetTree.LateCollapseSemantics as Semantics
import LogOS.Apps.ZFC.Models.IterativeSetTree.StagedReification as Stage

module For {ℓ : Level} (H : Stage.StageAssumptionsᵛ {ℓ}) where
  module W = Witnesses.For H
  module S = Semantics.For H

  canonicalRungᵛ = W.canonicalRungᵛ
  base = W.base

  Assumptions = W.Assumptions
  Completion = W.Completion

  foWitnessesᵛ = W.foWitnessesᵛ
  wfMemᵛ = W.wfMemᵛ
  structuralAssumptionsᵛ = W.structuralAssumptionsᵛ
  completionWitnessᵛ = W.completionWitnessᵛ

  completionLayerᵛ : Assumptions -> Comp.CompletionLayer canonicalRungᵛ
  completionLayerᵛ A =
    Comp.fromWitness (completionWitnessᵛ A)

  module ImplFor (A : Assumptions) where
    open S.Complete (completionWitnessᵛ A) public

  reifiedZFCFOᵛ : Assumptions → _
  reifiedZFCFOᵛ = S.reifiedZFCFOᵛ

  baseᵂ : Assumptions → Tower.ZFStackBase {lsuc ℓ}
  baseᵂ = S.baseᵂ

  stackFO₋Fnd : Assumptions → TowerFO.ZFCStackFO₋Fnd {lsuc ℓ}
  stackFO₋Fnd = S.stackFO₋Fnd

  stackFO : Assumptions → TowerFO.ZFCStackFO {lsuc ℓ}
  stackFO = S.stackFO

  proofModel : Assumptions → SemCore.Model {lsuc ℓ}
  proofModel = S.proofModel
