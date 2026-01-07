{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Arguments.TransformerKolmogorovScaling where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)

open import Data.Nat using (ℕ; _+_)
open import Data.NatOrder using (_≤ℕ_; dec≤ℕ; not≤→≥)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary; ConPoset)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel.Graded using (GradedKernel)
import LogOS.Kernel.Graded as GK

import LogOS.Domain.UniversalIR.Core.UCode as U
import LogOS.Domain.UniversalIR.Size as USize

import LogOS.Packs.Agents.Arguments.TransformerBridge as TransformerBridge
import LogOS.Packs.Agents.Learning.RGFlow as RGFlow
import LogOS.Packs.Agents.Arguments.ScalingLaws as ScalingLaws
import LogOS.Theorems.Meta.MathPhysSynthesis as MPS

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

  open GradedKernel K using (Code; decode; encode; decode∘encode)
  open QAdapter Q using (_≤s_; Scale)

  Dec : Set ℓ
  Dec = ConPoset.Con (BulkBoundary.bnd (GradedKernel.BB K))

  record UniversalIRCompile : Set (lsuc (lsuc ℓ)) where
    field
      compile : Code → U.UCode

    size : Code → ℕ
    size γ = USize.ucodeSize (compile (encode (decode γ)))

    size-ext : ∀ γ₁ γ₂ → decode γ₁ ≡ decode γ₂ → size γ₁ ≡ size γ₂
    size-ext γ₁ γ₂ decEq =
      cong (λ c → USize.ucodeSize (compile (encode c))) decEq

  record CodeBudget : Set (lsuc (lsuc ℓ)) where
    field
      B : Code → ℕ
      Bext : ∀ γ₁ γ₂ → decode γ₁ ≡ decode γ₂ → B γ₁ ≡ B γ₂

  kt : (Code → ℕ) → (Code → ℕ) → Code → ℕ
  kt size budget γ = size γ + budget γ

  KtOptimal : (Code → ℕ) → (Code → ℕ) → Code → Set ℓ
  KtOptimal size budget γ =
    ∀ δ → decode δ ≡ decode γ → kt size budget γ ≤ℕ kt size budget δ

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

    module O = MPS.Observer Code Dec decode (GK.FlowCode K)
                              (KtOptimalLoss obs size budget)
    open O using (Pr; Pr-ext; Pr-stable)

    DiscoverCode : Code → Set (lsuc (lsuc ℓ))
    DiscoverCode = Pr

    discover-reify : ∀ γ → DiscoverCode (GradedKernel.reify K γ) ↔ DiscoverCode γ
    discover-reify γ =
      let eq = GradedKernel.reify-decode K γ in
      record
        { to   = λ d → Pr-ext (GradedKernel.reify K γ) γ eq d
        ; from = λ d → Pr-ext γ (GradedKernel.reify K γ) (sym eq) d
        }

  record KolmogorovBridge {g : Scale} : Set (lsuc (lsuc ℓ)) where
    field
      train : TB.TrainingSpec g
      uir : UniversalIRCompile
      budget : CodeBudget
      lossObs : TB.LossObservableFromData (TB.TrainingSpec.bridge train)
      stable
        : ∀ {γ}
          → Obs.DiscoverCode
              (TB.LossObservableFromData.obs lossObs)
              (UniversalIRCompile.size uir)
              (CodeBudget.B budget)
              γ
          → RG.RGStable
              (TB.TransformerTrainingBridge.step (TB.trainingBridgeFromSpec train))
              (decode γ)

  open KolmogorovBridge public

  stepOf : ∀ {g} → KolmogorovBridge {g} → RG.RGStep g
  stepOf B =
    TB.TransformerTrainingBridge.step (TB.trainingBridgeFromSpec (KolmogorovBridge.train B))

  discovery-scalingBound
    : ∀ {g} (B : KolmogorovBridge {g})
    → ∀ {γ}
    → Obs.DiscoverCode
        (TB.LossObservableFromData.obs (lossObs B))
        (UniversalIRCompile.size (uir B))
        (CodeBudget.B (budget B))
        γ
    → SL.ScalingBound
        (TB.TransformerTrainingBridge.step (TB.trainingBridgeFromSpec (train B)))
        (TB.TransformerTrainingBridge.dim (TB.trainingBridgeFromSpec (train B)))
        γ
  discovery-scalingBound B d =
    SL.scalingBound-from-stable
      (TB.TransformerTrainingBridge.step (TB.trainingBridgeFromSpec (train B)))
      (TB.TransformerTrainingBridge.dim (TB.trainingBridgeFromSpec (train B)))
      (stable B d)

  record BudgetPhase (B : Code → ℕ) : Set (lsuc (lsuc ℓ)) where
    field
      cut : ℕ

    Low : Code → Set
    Low γ = B γ ≤ℕ cut

    High : Code → Set
    High γ = cut ≤ℕ B γ

  record TwoRegimeBridge {g : Scale} : Set (lsuc (lsuc ℓ)) where
    field
      base : KolmogorovBridge {g}
      phase : BudgetPhase (CodeBudget.B (KolmogorovBridge.budget base))
      dimLow : RG.ScalingDimension (stepOf base)
      dimHigh : RG.ScalingDimension (stepOf base)

  open TwoRegimeBridge public

  scalingLow
    : ∀ {g} (B : TwoRegimeBridge {g}) {γ}
    → Obs.DiscoverCode
        (TB.LossObservableFromData.obs (lossObs (base B)))
        (UniversalIRCompile.size (uir (base B)))
        (CodeBudget.B (budget (base B)))
        γ
    → BudgetPhase.Low (phase B) γ
    → SL.ScalingBound (stepOf (base B)) (dimLow B) γ
  scalingLow B d _ =
    SL.scalingBound-from-stable
      (stepOf (base B))
      (dimLow B)
      (stable (base B) d)

  scalingHigh
    : ∀ {g} (B : TwoRegimeBridge {g}) {γ}
    → Obs.DiscoverCode
        (TB.LossObservableFromData.obs (lossObs (base B)))
        (UniversalIRCompile.size (uir (base B)))
        (CodeBudget.B (budget (base B)))
        γ
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
      compute-ext : ∀ γ₁ γ₂ → decode γ₁ ≡ decode γ₂ → compute γ₁ ≡ compute γ₂
      data-ext : ∀ γ₁ γ₂ → decode γ₁ ≡ decode γ₂ → dataBudget γ₁ ≡ dataBudget γ₂

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

  record ChinchillaBridge {g : Scale} : Set (lsuc (lsuc ℓ)) where
    field
      base : KolmogorovBridge {g}
      budgets : ComputeDataBudget
      dimCompute : RG.ScalingDimension (stepOf base)
      dimData : RG.ScalingDimension (stepOf base)

  open ChinchillaBridge public

  compute-limited-scaling
    : ∀ {g} (B : ChinchillaBridge {g}) {γ}
    → Obs.DiscoverCode
        (TB.LossObservableFromData.obs (lossObs (base B)))
        (UniversalIRCompile.size (uir (base B)))
        (CodeBudget.B (budget (base B)))
        γ
    → ComputeDataBudget.ComputeLimited (budgets B) γ
    → SL.ScalingBound (stepOf (base B)) (dimCompute B) γ
  compute-limited-scaling B d _ =
    SL.scalingBound-from-stable
      (stepOf (base B))
      (dimCompute B)
      (stable (base B) d)

  data-limited-scaling
    : ∀ {g} (B : ChinchillaBridge {g}) {γ}
    → Obs.DiscoverCode
        (TB.LossObservableFromData.obs (lossObs (base B)))
        (UniversalIRCompile.size (uir (base B)))
        (CodeBudget.B (budget (base B)))
        γ
    → ComputeDataBudget.DataLimited (budgets B) γ
    → SL.ScalingBound (stepOf (base B)) (dimData B) γ
  data-limited-scaling B d _ =
    SL.scalingBound-from-stable
      (stepOf (base B))
      (dimData B)
      (stable (base B) d)

  chinchilla-compare
    : ∀ {g} (B : ChinchillaBridge {g}) {γ}
    → Obs.DiscoverCode
        (TB.LossObservableFromData.obs (lossObs (base B)))
        (UniversalIRCompile.size (uir (base B)))
        (CodeBudget.B (budget (base B)))
        γ
    → SL.ScalingBound (stepOf (base B)) (dimCompute B) γ
      ⊎ SL.ScalingBound (stepOf (base B)) (dimData B) γ
  chinchilla-compare B {γ} d with dec≤ℕ (ComputeDataBudget.compute (budgets B) γ) (ComputeDataBudget.dataBudget (budgets B) γ)
  ... | inj₁ comp≤data =
    inj₁ (compute-limited-scaling B d comp≤data)
  ... | inj₂ not≤ =
    inj₂ (data-limited-scaling B d (not≤→≥ not≤))
