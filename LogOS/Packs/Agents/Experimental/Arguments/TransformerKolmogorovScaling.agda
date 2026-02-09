{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Arguments.TransformerKolmogorovScaling where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)

open import LogOS.Prelude using (ℕ; _+_)
open import LogOS.Prelude.NatOrder using (_≤ℕ_; dec≤ℕ; not≤→≥)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary; ConPreorder)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel.Graded using (GradedKernel)
import LogOS.Kernel.Graded as GK
open import LogOS.Kernel.Eq using (module ForGradedKernel)

import LogOS.Packs.Agents.Experimental.Arguments.TransformerBridge as TransformerBridge
import LogOS.Packs.Agents.Experimental.Learning.RGFlow as RGFlow
import LogOS.Packs.Agents.Experimental.Arguments.ScalingLaws as ScalingLaws
import LogOS.Packs.Agents.Experimental.Arguments.Context as Ctx

-- Kolmogorov/Kt-optimal discovery aligned with the transformer bridge.

module For
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO)
            (BulkBoundary.bnd (GradedKernel.BB K)))
  where

  module TB = TransformerBridge.For K ωCPO
  module RG = RGFlow.For K ωCPO
  module SL = ScalingLaws.For K ωCPO

  open GradedKernel K using (Code; decode; reify)
  open ForGradedKernel K
  open QAdapter Q using (_≤s_; Scale)

  Dec : Set ℓ
  Dec = ConPreorder.Con (BulkBoundary.bnd (GradedKernel.BB K))

  record UniversalIRCompile : Set (lsuc (lsuc ℓ)) where
    field
      size : Code → ℕ
      size-ext : ∀ γ₁ γ₂ → γ₁ ≃K γ₂ → size γ₁ ≡ size γ₂

  record CodeBudget : Set (lsuc (lsuc ℓ)) where
    field
      B : Code → ℕ
      Bext : ∀ γ₁ γ₂ → γ₁ ≃K γ₂ → B γ₁ ≡ B γ₂

  kt : (Code → ℕ) → (Code → ℕ) → Code → ℕ
  kt size budget γ = size γ + budget γ

  KtOptimal : (Code → ℕ) → (Code → ℕ) → Code → Set ℓ
  KtOptimal size budget γ =
    ∀ δ → δ ≃K γ → kt size budget γ ≤ℕ kt size budget δ

  KtOptimalLoss
    : (obs : Dec → Scale)
    → (size : Code → ℕ)
    → (budget : Code → ℕ)
    → Code → Set ℓ
  KtOptimalLoss obs size budget γ =
    ∀ δ
    → _≤s_ (obs (decode δ)) (obs (decode γ))
    → kt size budget γ ≤ℕ kt size budget δ

  module Obs
    (obs : Dec → Scale)
    (size : Code → ℕ)
    (budget : Code → ℕ)
    where

    record ResidualBoundary : Set (lsuc (lsuc ℓ)) where
      field
        Resid : Set ℓ
        residual : Dec → Resid

    record ResidualDiscovery : Set (lsuc (lsuc (lsuc ℓ))) where
      field
        boundary : ResidualBoundary
        DiscoverResidual
          : ResidualBoundary.Resid boundary
          → Set (lsuc (lsuc ℓ))
        reify-invariant
          : ∀ γ
          → DiscoverResidual
              (ResidualBoundary.residual boundary (decode (reify γ)))
            ↔ DiscoverResidual
                (ResidualBoundary.residual boundary (decode γ))

    DiscoverCode : ResidualDiscovery → Code → Set (lsuc (lsuc ℓ))
    DiscoverCode D γ =
      ResidualDiscovery.DiscoverResidual D
        (ResidualBoundary.residual
          (ResidualDiscovery.boundary D)
          (decode γ))

    discover-residual
      : ∀ (D : ResidualDiscovery) {γ δ}
      → ResidualBoundary.residual (ResidualDiscovery.boundary D) (decode γ)
          ≡ ResidualBoundary.residual (ResidualDiscovery.boundary D) (decode δ)
      → DiscoverCode D γ
      → DiscoverCode D δ
    discover-residual D eq d =
      subst
        (ResidualDiscovery.DiscoverResidual D)
        eq
        d

    discover-reify
      : ∀ (D : ResidualDiscovery) γ
      → DiscoverCode D (reify γ) ↔ DiscoverCode D γ
    discover-reify D γ = ResidualDiscovery.reify-invariant D γ

  record KolmogorovBridge {g : Scale} : Set (lsuc (lsuc (lsuc ℓ))) where
    field
      train : TB.Training.TrainingSpec g
      uir : UniversalIRCompile
      budget : CodeBudget
      discovery
        : Obs.ResidualDiscovery
            (TB.Training.LossObservableFromData.obs (TB.Training.TrainingSpec.lossObsData train))
            (UniversalIRCompile.size uir)
            (CodeBudget.B budget)
      stable
        : ∀ {γ}
          → Obs.DiscoverCode
              (TB.Training.LossObservableFromData.obs (TB.Training.TrainingSpec.lossObsData train))
              (UniversalIRCompile.size uir)
              (CodeBudget.B budget)
              discovery
              γ
          → RG.RGStable
              (TB.Training.TransformerTrainingBridge.step (TB.Training.trainingBridgeFromSpec train))
              (decode γ)

  open KolmogorovBridge public

  stepOf : ∀ {g} → KolmogorovBridge {g} → RG.RGStep g
  stepOf B =
    TB.Training.TransformerTrainingBridge.step (TB.Training.trainingBridgeFromSpec (KolmogorovBridge.train B))

  dimOf : ∀ {g} → (B : KolmogorovBridge {g}) → RG.ScalingDimension (stepOf B)
  dimOf B =
    TB.Training.TransformerTrainingBridge.dim (TB.Training.trainingBridgeFromSpec (train B))

  DiscoverAt : ∀ {g} (B : KolmogorovBridge {g}) → Code → Set (lsuc (lsuc ℓ))
  DiscoverAt B =
    Obs.DiscoverCode
      (TB.Training.LossObservableFromData.obs (TB.Training.TrainingSpec.lossObsData (train B)))
      (UniversalIRCompile.size (uir B))
      (CodeBudget.B (budget B))
      (discovery B)

  discovery-scalingBound
    : ∀ {g} (B : KolmogorovBridge {g})
    → ∀ {γ}
    → DiscoverAt B γ
    → SL.ScalingBound
        (stepOf B)
        (dimOf B)
        γ
  discovery-scalingBound B d =
    SL.scalingBound-from-stable
      (stepOf B)
      (dimOf B)
      (stable B d)

  record BudgetPhase (B : Code → ℕ) : Set (lsuc (lsuc ℓ)) where
    field
      cut : ℕ

    Low : Code → Set
    Low γ = B γ ≤ℕ cut

    High : Code → Set
    High γ = cut ≤ℕ B γ

  record TwoRegimeBridge {g : Scale} : Set (lsuc (lsuc (lsuc ℓ))) where
    field
      base : KolmogorovBridge {g}
      phase : BudgetPhase (CodeBudget.B (KolmogorovBridge.budget base))
      dimLow : RG.ScalingDimension (stepOf base)
      dimHigh : RG.ScalingDimension (stepOf base)

  open TwoRegimeBridge public

  scalingLow
    : ∀ {g} (B : TwoRegimeBridge {g}) {γ}
    → DiscoverAt (base B) γ
    → BudgetPhase.Low (phase B) γ
    → SL.ScalingBound (stepOf (base B)) (dimLow B) γ
  scalingLow B d _ =
    SL.scalingBound-from-stable
      (stepOf (base B))
      (dimLow B)
      (stable (base B) d)

  scalingHigh
    : ∀ {g} (B : TwoRegimeBridge {g}) {γ}
    → DiscoverAt (base B) γ
    → BudgetPhase.High (phase B) γ
    → SL.ScalingBound (stepOf (base B)) (dimHigh B) γ
  scalingHigh B d _ =
    SL.scalingBound-from-stable
      (stepOf (base B))
      (dimHigh B)
      (stable (base B) d)

  record ComputeDataBudget : Set (lsuc (lsuc ℓ)) where
    field
      compute : Code → ℕ
      dataBudget : Code → ℕ
      compute-ext : ∀ γ₁ γ₂ → γ₁ ≃K γ₂ → compute γ₁ ≡ compute γ₂
      data-ext : ∀ γ₁ γ₂ → γ₁ ≃K γ₂ → dataBudget γ₁ ≡ dataBudget γ₂

    ComputeLimited : Code → Set
    ComputeLimited γ = compute γ ≤ℕ dataBudget γ

    DataLimited : Code → Set
    DataLimited γ = dataBudget γ ≤ℕ compute γ

  codeBudget-from-resources
    : ∀ {B : TB.TransformerKernelBridge}
    → TB.ResourceBudgets B
    → CodeBudget
  codeBudget-from-resources R =
    record
      { B = TB.ResourceBudgets.compute R
      ; Bext = TB.ResourceBudgets.compute-ext R
      }

  computeDataBudget-from-resources
    : ∀ {B : TB.TransformerKernelBridge}
    → TB.ResourceBudgets B
    → ComputeDataBudget
  computeDataBudget-from-resources R =
    record
      { compute = TB.ResourceBudgets.compute R
      ; dataBudget = TB.ResourceBudgets.dataBudget R
      ; compute-ext = TB.ResourceBudgets.compute-ext R
      ; data-ext = TB.ResourceBudgets.data-ext R
      }

  record ChinchillaBridge {g : Scale} : Set (lsuc (lsuc (lsuc ℓ))) where
    field
      base : KolmogorovBridge {g}
      budgets : ComputeDataBudget
      dimCompute : RG.ScalingDimension (stepOf base)
      dimData : RG.ScalingDimension (stepOf base)

  open ChinchillaBridge public

  compute-limited-scaling
    : ∀ {g} (B : ChinchillaBridge {g}) {γ}
    → DiscoverAt (base B) γ
    → ComputeDataBudget.ComputeLimited (budgets B) γ
    → SL.ScalingBound (stepOf (base B)) (dimCompute B) γ
  compute-limited-scaling B d _ =
    SL.scalingBound-from-stable
      (stepOf (base B))
      (dimCompute B)
      (stable (base B) d)

  data-limited-scaling
    : ∀ {g} (B : ChinchillaBridge {g}) {γ}
    → DiscoverAt (base B) γ
    → ComputeDataBudget.DataLimited (budgets B) γ
    → SL.ScalingBound (stepOf (base B)) (dimData B) γ
  data-limited-scaling B d _ =
    SL.scalingBound-from-stable
      (stepOf (base B))
      (dimData B)
      (stable (base B) d)

  chinchilla-compare
    : ∀ {g} (B : ChinchillaBridge {g}) {γ}
    → DiscoverAt (base B) γ
    → SL.ScalingBound (stepOf (base B)) (dimCompute B) γ
      ⊎ SL.ScalingBound (stepOf (base B)) (dimData B) γ
  chinchilla-compare B {γ} d with dec≤ℕ (ComputeDataBudget.compute (budgets B) γ) (ComputeDataBudget.dataBudget (budgets B) γ)
  ... | inj₁ comp≤data =
    inj₁ (compute-limited-scaling B d comp≤data)
  ... | inj₂ not≤ =
    inj₂ (data-limited-scaling B d (not≤→≥ not≤))

-- Context-bundled entrypoint (convenience).
module ForCtx
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (C : Ctx.Context Sig Q)
  where
  open For (Ctx.Context.K C) (Ctx.Context.ωCPO C) public
