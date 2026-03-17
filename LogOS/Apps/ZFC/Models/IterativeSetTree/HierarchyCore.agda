{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Models.IterativeSetTree.HierarchyCore where

-- Coherent iterative-tree hierarchy section across universe levels.
--
-- This canonical core packages only stage assumptions, canonical rungs, and
-- successor-stage bridge data. Completion transport is factored out into
-- `HierarchyCompletion`.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (refl⊑)
open import LogOS.LT.Stage.SuccessorChain using (levelChain)
open import LogOS.LT.Stage.Section as Sec using (Section)

import LogOS.Apps.ZFC.Stack.AsymptoticReification as AR
import LogOS.Apps.ZFC.Stack.AsymptoticReification.CanonicalRung as ZR
import LogOS.Apps.ZFC.Stack.AsymptoticReification.SuccessorBridge as Bridge
import LogOS.Apps.ZFC.Stack.AsymptoticReification.SuccessorHierarchy as ZH

import LogOS.Apps.ZFC.Models.IterativeSetTree.Context as Ctx
import LogOS.Apps.ZFC.Models.IterativeSetTree.HierarchyInfinity as Inf
import LogOS.Apps.ZFC.Models.IterativeSetTree.StagedReification as Stage
import LogOS.Apps.ZFC.Models.IterativeSetTree.SuccessorTruthLift as Lift

canonicalRungFromAssumptionsᵛ
  : ∀ {ℓ : Level}
  -> Stage.StageAssumptionsᵛ {ℓ}
  -> ZR.CanonicalRung (Ctx.ctxᵛ {ℓ})
canonicalRungFromAssumptionsᵛ {ℓ} A =
  let
    module Stageℓ = Stage.For A
    module Infℓ = Inf.For A
    module Rℓ = AR.PredicateReification (AR.staged→restricted Stageℓ.stagedPredicateReificationᵛ)
  in
  record
    { staged = Stageℓ.stagedPredicateReificationᵛ
    ; collapse = λ _ -> refl⊑ Rℓ.PredBnd
    ; baseAssumptions = Infℓ.baseAssumptions
    }

record StageSemanticsᵛ (ℓ : Level) : Set (lsuc (lsuc (lsuc ℓ))) where
  field
    assumptionsᵛ : Stage.StageAssumptionsᵛ {ℓ}
    canonicalRungᵛ : ZR.CanonicalRung (Ctx.ctxᵛ {ℓ})
    canonicalRung-okᵛ : canonicalRungᵛ ≡ canonicalRungFromAssumptionsᵛ assumptionsᵛ

mkStageSemanticsᵛ
  : ∀ {ℓ : Level}
  -> Stage.StageAssumptionsᵛ {ℓ}
  -> StageSemanticsᵛ ℓ
mkStageSemanticsᵛ A =
  record
    { assumptionsᵛ = A
    ; canonicalRungᵛ = canonicalRungFromAssumptionsᵛ A
    ; canonicalRung-okᵛ = refl
    }

open StageSemanticsᵛ public using (assumptionsᵛ; canonicalRungᵛ)

HierarchySectionᵛ : Setω
HierarchySectionᵛ = Sec.Section levelChain StageSemanticsᵛ

module For (H : HierarchySectionᵛ) where
  open Sec.Section H using (at)

  private
    stageAt : (ℓ : Level) -> StageSemanticsᵛ ℓ
    stageAt = at

    assumptionsAt : (ℓ : Level) -> Stage.StageAssumptionsᵛ {ℓ}
    assumptionsAt ℓ = assumptionsᵛ (stageAt ℓ)

    rungAtᵛ : (ℓ : Level) -> ZR.CanonicalRung (Ctx.ctxᵛ {ℓ})
    rungAtᵛ ℓ = StageSemanticsᵛ.canonicalRungᵛ (stageAt ℓ)

    SuccessorBridgeAtᵛ : (ℓ : Level) -> Set (lsuc (lsuc (lsuc (lsuc ℓ))))
    SuccessorBridgeAtᵛ ℓ = Bridge.SuccessorBridge (ZR.CanonicalRung.base (rungAtᵛ ℓ)) (Ctx.ctxᵛ {lsuc ℓ})

  hierarchyᵛ : ZH.SuccessorHierarchy levelChain
  hierarchyᵛ =
    record
      { ctxLevel = lsuc
      ; ctxAt = λ ℓ -> Ctx.ctxᵛ {ℓ}
      ; rungAt = rungAtᵛ
      ; successorBridge = successorBridgeᵛ
      }
    where
      successorBridgeᵛ : (ℓ : Level) -> SuccessorBridgeAtᵛ ℓ
      successorBridgeᵛ ℓ rewrite StageSemanticsᵛ.canonicalRung-okᵛ (stageAt ℓ) =
        let
          module Liftℓ = Lift.For (assumptionsAt ℓ)
          module Liftedℓ = Liftℓ.WithLiftedImages
            (Stage.StageAssumptionsᵛ.collapse (assumptionsAt (lsuc ℓ)))
          module Infℓ = Inf.For (assumptionsAt ℓ)
          module Baseℓ = Liftedℓ.ForBase Infℓ.baseAssumptions
        in
        record
          { reification = Liftℓ.crossStagePredicateReificationᵛ
          ; foWitnesses = Baseℓ.foWitnesses↑
          }
