{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.CHL.ModelTheory where

-- Model-theory view: refinement implies semantic entailment at the H/boundary tiers.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Base.Signature.Hom using (SigHom)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Truth as Truth
open import LogOS.Syntax.Prop as Prop using (_↔_)

open import LogOS.Kernel hiding (Box; decode-Box; box-mono)
import LogOS.Theorems.Meta.CHL.Core as CHL
import LogOS.Theorems.Meta.CHL.Completeness as Complete
import LogOS.Theorems.Meta.CHL.SyntaxCompleteness as Syntax
import LogOS.Theorems.Meta.CHL.ViewTheorems as ViewTheorems
import LogOS.Theorems.Meta.ConditionalPacks as ConditionalPacks
import LogOS.Theorems.Meta.SemanticsTransport as SemTransport
import LogOS.Theorems.Meta.SpectralSeparationOutput as SpectralSeparationOutput
import LogOS.Theorems.Meta.BudgetedSeparationOutput as BudgetedSeparationOutput
import LogOS.Ports.Semantic.Interoperability as Interoperability
import LogOS.Ports.Semantic.InterlinguaStrictReindex as StrictReindex

module For
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  where

  module C = CHL.For K
  open C
  module Co = Complete.For K
  module S = Syntax.For K
  module V = ViewTheorems.For K

  module HT = Truth.HomotypicalTruth Sig Q (Kernel.HWorld K)

  module Profiles where
    open Co public
      using
        ( BoundaryAdequacy
        ; BoundaryObsAdequacy
        ; ObsAdequacy
        ; Budget
        ; BudgetedAdequacy
        )

  module AdequacyProfiles = Profiles

  module LayeredInstitution where
    module MultiInstitution = V.MultiInstitution
    open V.MultiInstitution public using (coh-SH; coh-H∂)
    module SentenceLayer = V.MultiInstitution.SentenceLayer

    module Reindex = ViewTheorems.Reindex
    module ReindexWithFml = ViewTheorems.ReindexWithFml
    module ReindexingSatisfaction = ViewTheorems.ReindexingSatisfaction
    module ReindexingSatisfactionWithFml = ViewTheorems.ReindexingSatisfactionWithFml
    module ReindexingSatisfactionWithFmlLogic = ViewTheorems.ReindexingSatisfactionWithFmlLogic

  module RepresentationIndependence where
    DecodeExtensional
      : ∀ {ℓP}
      → (P : Kernel.Code K → Set ℓP)
      → Set (ℓ ⊔ ℓP)
    DecodeExtensional = ConditionalPacks.DecodeExtensional K

    DecodeExtensional≈
      : ∀ {ℓP}
      → (P : Kernel.Code K → Set ℓP)
      → Set (ℓ ⊔ ℓP)
    DecodeExtensional≈ = ConditionalPacks.DecodeExtensional≈ K

    DecodeExtensionalFn
      : ∀ {ℓX} {X : Set ℓX}
      → (f : Kernel.Code K → X)
      → Set (ℓ ⊔ ℓX)
    DecodeExtensionalFn = ConditionalPacks.DecodeExtensionalFn K

    DecodeExtensionalFn≈
      : ∀ {ℓX} {X : Set ℓX}
      → (f : Kernel.Code K → X)
      → Set (ℓ ⊔ ℓX)
    DecodeExtensionalFn≈ = ConditionalPacks.DecodeExtensionalFn≈ K

    module SemanticsTransport = SemTransport
    module PortInteroperability = Interoperability

    module ForStrictReindex
      {Sig₁ : LogOSSignature ℓ}
      (σ : SigHom Sig₁ Sig)
      {Fml₁ : Set ℓ}
      (mapFml : Fml₁ → Kernel.Fml K)
      where
      module SR = StrictReindex.ForKernel σ K mapFml
      open SR public using (translate≈mapFml; mapFml-preserves-Sat; mapFml-unique)

  module RelativeCompleteness where
    open S public
      using
        ( _⊢S_
        ; EntailsS
        ; EntailsS-budget
        ; soundS
        ; completeS
        ; sound-completeS
        ; sound-completeS-obs
        ; sound-completeS-budget
        )

    module ForStrictReindex
      {Sig₁ : LogOSSignature ℓ}
      (σ : SigHom Sig₁ Sig)
      {Fml₁ : Set ℓ}
      (mapFml : Fml₁ → Kernel.Fml K)
      where
      module RS = ViewTheorems.ReindexingSatisfactionWithFml σ K mapFml
      module SR = StrictReindex.ForKernel σ K mapFml

      open RS public using (SatS-precompose)
      open SR public using (translate≈mapFml; mapFml-preserves-Sat; mapFml-unique)

      complete-mapFml
        : Co.BoundaryAdequacy
        → ∀ {φ ψ}
        → EntailsS (mapFml φ) (mapFml ψ)
        → (mapFml φ) ⊢S (mapFml ψ)
      complete-mapFml BA {φ} {ψ} ent =
        completeS BA {φ = mapFml φ} {ψ = mapFml ψ} ent

      sound-complete-mapFml
        : Co.BoundaryAdequacy
        → ∀ {φ ψ}
        → ((mapFml φ) ⊢S (mapFml ψ)) ↔ EntailsS (mapFml φ) (mapFml ψ)
      sound-complete-mapFml BA {φ} {ψ} =
        sound-completeS BA {φ = mapFml φ} {ψ = mapFml ψ}

  module BoundaryLayer where
    open Co public
      using
        ( Entails∂
        ; Entails∂-budget
        ; sound∂
        ; complete∂
        ; sound-complete∂
        ; sound-complete∂-budget
        )

  module StrictLayer where
    open S public
      using
        ( _⊢S_
        ; EntailsS
        ; EntailsS-budget
        ; soundS
        ; completeS
        ; sound-completeS
        ; sound-completeS-budget
        )

  module SeparationBoundary where
    SpectralSeparation = SpectralSeparationOutput.SpectralSeparationOutput
    SeparationOracle = SpectralSeparationOutput.Oracle
    SeparationTotalityClaim = SpectralSeparationOutput.SeparationTotalityClaim

    separation-not-total = SpectralSeparationOutput.separation-output-not-total
    separation-no-self-certification = SpectralSeparationOutput.separation-output-no-self-certification
    separation-diagonal-witness = SpectralSeparationOutput.separation-output-diagonal-witness

    module GeneralBudget = SpectralSeparationOutput.GeneralB

    WitnessCost = BudgetedSeparationOutput.WitnessCost
    Witness≤ = BudgetedSeparationOutput.Witness≤
    Budgeted = BudgetedSeparationOutput.Budgeted
    BudgetedBy = BudgetedSeparationOutput.BudgetedBy
    UniformBudget = BudgetedSeparationOutput.UniformBudget
    uniformBudget→budgetedTotal = BudgetedSeparationOutput.uniformBudget→budgetedTotal
    budgeted-diagonal-witness = BudgetedSeparationOutput.budgeted-diagonal-witness
    no-uniform-budget = BudgetedSeparationOutput.no-uniform-budget
    no-total-within = BudgetedSeparationOutput.no-total-within

  -- Refinement implies H-tier entailment.
  entails-H
    : ∀ {gamma delta}
    → Refines gamma delta
    → ∀ (w : LogOSSignature.Cosp Sig)
    → HT.HLayer.Sat_H (Kernel.HTruth K) w (denote gamma)
    → HT.HLayer.Sat_H (Kernel.HTruth K) w (denote delta)
  entails-H le _ sat =
    HT.HLayer.mono-Con (Kernel.HTruth K) le sat

  -- Refinement implies boundary entailment (via sat-coh).
  entails-boundary
    : ∀ {gamma delta}
    → Refines gamma delta
    → Co.Entails∂ gamma delta
  entails-boundary = Co.sound∂
