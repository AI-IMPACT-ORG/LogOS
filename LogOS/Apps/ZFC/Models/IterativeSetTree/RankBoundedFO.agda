{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Models.IterativeSetTree.RankBoundedFO where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)

import LogOS.Apps.ZFC.Stack.AsymptoticReification as AR
import LogOS.Apps.ZFC.Stack.AsymptoticReification.LocalPresentationFO as LocalPresentationFO
import LogOS.Apps.ZFC.Proof.Syntax as Syn
import LogOS.Apps.ZFC.Stack.ProfileTower.Core as Tower
import LogOS.Apps.ZFC.Stack.ZFCore as ZF

import LogOS.Apps.ZFC.Models.IterativeSetTree.PresentationAdapters as Adapt
import LogOS.Apps.ZFC.Models.IterativeSetTree.Rank as Rank
import LogOS.Apps.ZFC.Models.IterativeSetTree.StageSetup as Setup
import LogOS.Apps.ZFC.Models.IterativeSetTree.StagedReification as Stage

module For {ℓ : Level} (H : Stage.StageAssumptionsᵛ {ℓ}) where
  module Setupᵛ = Setup.For H
  open Setupᵛ using
    ( C
    ; collapse
    ; stagedPredicateReificationᵛ
    ; restrictedPredicateReificationᵛ
    ; collapseFlowᵛ
    )
  module Adaptᵛ = Adapt.For collapse
  module LC = Setupᵛ.LC

  module Collapse = LC.WithFlowCollapse collapseFlowᵛ

  module ForBase (B₀ : LC.BaseAssumptions) where
    module Bundle = Collapse.ForBase B₀

    private
      B : Tower.ZFStackBase {lsuc ℓ}
      B = Bundle.base

    module FO = AR.FO B restrictedPredicateReificationᵛ
    module StageFO = AR.StagedFO B stagedPredicateReificationᵛ
    open Tower.ZFStackBase B using (SetU; _∈_; _≈_)

    module LocalFO = LocalPresentationFO.ForPresentation
      B
      stagedPredicateReificationᵛ
      Adaptᵛ.localGeneratorsᵛ
      Adaptᵛ.generatedSubtreesᵛ
      Adaptᵛ.generatedImagesᵛ

    stageClassifierᵛ : LocalFO.StageClassifier
    stageClassifierᵛ =
      record
        { stageOf = λ x spec →
            Rank.rankᵛ x
            , ( x
              , ( Rank.≤ʳ-refl
                , spec
                )
              )
        }

    predicateTransportᵛ : LocalFO.PredicateTransport
    predicateTransportᵛ = LocalFO.strictPredicateTransport (Stage.ExtensionalCollapseᵛ.extensionalityᵛ collapse)

    refinedSubobjectsᵛ : LocalFO.RefinedGeneratedSubobjects
    refinedSubobjectsᵛ = Adaptᵛ.generatedSubtreesᵛ

    relationTransportᵛ : LocalFO.RelationTransport
    relationTransportᵛ = LocalFO.strictRelationTransport (Stage.ExtensionalCollapseᵛ.extensionalityᵛ collapse)

    refinedImagesᵛ : LocalFO.RefinedGeneratedImages
    refinedImagesᵛ = Adaptᵛ.generatedImagesᵛ

    SepClassifierᵛ : Set (lsuc (lsuc (lsuc ℓ)))
    SepClassifierᵛ = LocalFO.SepClassifier

    sepSet
      : SepClassifierᵛ
      → (P : Syn.Formula)
      → FO.FB.Valuation
      → SetU
      → SetU
    sepSet = LocalFO.sepSet refinedSubobjectsᵛ

    sepSet-spec
      : ∀ (C : SepClassifierᵛ) (P : Syn.Formula) (ρ : FO.FB.Valuation) (x z : SetU)
      → (z ∈ sepSet C P ρ x) ↔ FO.SepPred P ρ x z
    sepSet-spec =
      LocalFO.sepSet-spec predicateTransportᵛ refinedSubobjectsᵛ

    repSet
      : (R₀ : Syn.Formula)
      → (ρ : FO.FB.Valuation)
      → (x : SetU)
      → FO.FB.FunctionalOnX R₀ ρ x
      → SetU
    repSet = LocalFO.repSet refinedImagesᵛ

    repSet-spec
      : ∀ (R₀ : Syn.Formula) (ρ : FO.FB.Valuation) (x z : SetU)
      → (fun : FO.FB.FunctionalOnX R₀ ρ x)
      → (z ∈ repSet R₀ ρ x fun) ↔ FO.RepPred R₀ ρ x z
    repSet-spec = LocalFO.repSet-spec relationTransportᵛ refinedImagesᵛ

    FORepresentabilityᵛ : Set (lsuc (lsuc (lsuc ℓ)))
    FORepresentabilityᵛ = LocalFO.FORepresentability

    stagedFOWitnesses
      : FORepresentabilityᵛ
      → StageFO.StagedFOWitnesses
    stagedFOWitnesses =
      LocalFO.stagedFOWitnesses
        predicateTransportᵛ
        refinedSubobjectsᵛ
        relationTransportᵛ
        refinedImagesᵛ
        stageClassifierᵛ

    foWitnesses
      : FORepresentabilityᵛ
      → FO.FOWitnesses
    foWitnesses =
      LocalFO.foWitnesses
        predicateTransportᵛ
        refinedSubobjectsᵛ
        relationTransportᵛ
        refinedImagesᵛ
        stageClassifierᵛ
