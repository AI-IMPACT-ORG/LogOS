{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Models.IterativeSetTree.LateCollapseSemantics where

-- Realised same-stage semantics for one iterative-tree rung.

open import LogOS.Prelude

import LogOS.Apps.ZFC.Stack.AsymptoticReification.CompletionSemantics as Comp
import LogOS.Apps.ZFC.Proof.Semantics.Core as SemCore
import LogOS.Apps.ZFC.Stack.ProfileTower.Core as Tower
import LogOS.Apps.ZFC.Stack.ProfileTowerFO as TowerFO

import LogOS.Apps.ZFC.Models.IterativeSetTree.LateCollapseAssumptions as Witnesses
import LogOS.Apps.ZFC.Models.IterativeSetTree.StagedReification as Stage

module For {ℓ : Level} (H : Stage.StageAssumptionsᵛ {ℓ}) where
  module W = Witnesses.For H

  Assumptions = W.Assumptions
  Completion = W.Completion
  completionWitnessᵛ = W.completionWitnessᵛ

  module Complete (A : Completion) where
    open Comp.Complete W.canonicalRungᵛ A public

  reifiedZFCFOᵛ : Assumptions → _
  reifiedZFCFOᵛ A =
    let module I = Complete (completionWitnessᵛ A) in
    I.reifiedZFCFO

  baseᵂ : Assumptions → Tower.ZFStackBase {lsuc ℓ}
  baseᵂ A =
    let module I = Complete (completionWitnessᵛ A) in
    I.baseᵂ

  stackFO₋Fnd : Assumptions → TowerFO.ZFCStackFO₋Fnd {lsuc ℓ}
  stackFO₋Fnd A =
    let module I = Complete (completionWitnessᵛ A) in
    I.stackFO₋Fnd

  stackFO : Assumptions → TowerFO.ZFCStackFO {lsuc ℓ}
  stackFO A =
    let module I = Complete (completionWitnessᵛ A) in
    I.stackFO

  proofModel : Assumptions → SemCore.Model {lsuc ℓ}
  proofModel A =
    let module I = Complete (completionWitnessᵛ A) in
    I.proofModel
