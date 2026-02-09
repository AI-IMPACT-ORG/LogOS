{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Arguments.TransformerScalingPipeline.Core where

open import LogOS.Prelude

open import LogOS.Prelude using (Σ; _,_; proj₁; proj₂)
open import LogOS.Prelude using (ℕ; zero; suc; _+_; _*_)
open import LogOS.Prelude.NatOrder using (_≤ℕ_; dec≤ℕ; not≤→≥)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary; ConPreorder)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel.Graded using (GradedKernel)
import LogOS.Computation.Core as Comp

import LogOS.Packs.Agents.Experimental.Arguments.TransformerBridge as TransformerBridge
import LogOS.Packs.Agents.Experimental.Learning.RGFlow as RGFlow
import LogOS.Packs.Agents.Experimental.Arguments.ScalingLaws as ScalingLaws
import LogOS.Packs.Agents.Experimental.Arguments.ControlledFeedback as ControlledFeedback

-- Unified, LogOS-aligned pipeline:
-- - loss dynamics define stability at the RG level,
-- - stability yields scaling bounds,
-- - discovery selects the observable fragment,
-- - resource budgets split compute/data regimes.
--
-- Architecture note: the theorem path only depends on the
-- ControlledFeedback abstraction; transformer specifics stay in bridge layers.

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
  module CF = ControlledFeedback.For K ωCPO

  open GradedKernel K using (Code; decode)
  open QAdapter Q using (Scale; _≤s_)
  open RG using (Policy; RGStep; RGStable; ScalingDimension; applyRG)

  Dec : Set ℓ
  Dec = ConPreorder.Con (BulkBoundary.bnd (GradedKernel.BB K))

  record UniversalIRCompile : Set (lsuc (lsuc ℓ)) where
    field
      size : Code → ℕ

  record ComputeDataBudget : Set (lsuc (lsuc ℓ)) where
    field
      compute : Code → ℕ
      dataBudget : Code → ℕ

    ComputeLimited : Code → Set
    ComputeLimited γ = compute γ ≤ℕ dataBudget γ

    DataLimited : Code → Set
    DataLimited γ = dataBudget γ ≤ℕ compute γ

  computeDataBudget-from-resources
    : ∀ {B : TB.KernelBridge.TransformerKernelBridge}
    → TB.Resources.ResourceBudgets B
    → ComputeDataBudget
  computeDataBudget-from-resources R =
    record
      { compute = TB.Resources.ResourceBudgets.compute R
      ; dataBudget = TB.Resources.ResourceBudgets.dataBudget R
      }

  record BudgetPhase (budget : Code → ℕ) : Set (lsuc (lsuc ℓ)) where
    field
      cut : ℕ

    Low : Code → Set
    Low γ = budget γ ≤ℕ cut

    High : Code → Set
    High γ = cut ≤ℕ budget γ

  record ResidualBoundary : Set (lsuc (lsuc ℓ)) where
    field
      Resid : Set ℓ
      residual : Policy → Resid

  LossMonotone : ∀ {g} (s : RGStep g) → (Policy → Scale) → Set ℓ
  LossMonotone s obs =
    ∀ c → _≤s_ (obs (applyRG s c)) (obs c)

  record LossDynamics {g : Scale} (s : RGStep g) : Set (lsuc (lsuc ℓ)) where
    field
      dim : ScalingDimension s
      order : TB.Training.LossOrderReflecting (ScalingDimension.obs dim)
      decrease : LossMonotone s (ScalingDimension.obs dim)

  loss-stable
    : ∀ {g} {s : RGStep g} (L : LossDynamics s) (c : Policy)
    → RGStable s c
  loss-stable L c =
    TB.Training.lossDecrease-stable
      (ScalingDimension.obs (LossDynamics.dim L))
      (LossDynamics.order L)
      (LossDynamics.decrease L)
      c

  loss-scaling
    : ∀ {g} {s : RGStep g} (L : LossDynamics s) {γ}
    → SL.ScalingBound s (LossDynamics.dim L) γ
  loss-scaling {s = s} L {γ} =
    SL.scalingBound-from-stable s (LossDynamics.dim L) (loss-stable L (decode γ))

  nextTokenLossDynamics
    : ∀ {g} {s : RGStep g} {B : TB.KernelBridge.TransformerKernelBridge}
    → (L : TB.Training.NextTokenLossObservableFromData B)
    → TB.Training.LossOrderReflecting (TB.Training.NextTokenLossObservableFromData.obs L)
    → LossMonotone s (TB.Training.NextTokenLossObservableFromData.obs L)
    → LossDynamics s
  nextTokenLossDynamics {s = s} L order dec =
    let L' = TB.Training.NextTokenLossObservableFromData.asLossObservableFromData L
        dim = TB.Training.scalingDimensionFromLoss {s = s}
                (TB.Training.LossObservableFromData.asLossObservable L')
    in record
      { dim = dim
      ; order = order
      ; decrease = dec
      }

  record PipelineAssumptions {g : Scale} : Set (lsuc (lsuc (lsuc ℓ))) where
    field
      spec : TB.Training.TrainingSpec g
      lossOrder
        : TB.Training.LossOrderReflecting
            (TB.Training.LossObservableFromData.obs (TB.Training.TrainingSpec.lossObsData spec))
      lossMonotone
        : ∀ p
        → _≤s_
            (TB.Loss.lossParam
              (TB.Training.LossObservableFromData.lossData (TB.Training.TrainingSpec.lossObsData spec))
              (TB.Training.TrainingSpec.trainParam spec p))
            (TB.Loss.lossParam
              (TB.Training.LossObservableFromData.lossData (TB.Training.TrainingSpec.lossObsData spec)) p)
      uir : UniversalIRCompile
      resources
        : TB.Resources.ResourceBudgets (TB.Training.TrainingSpec.bridge spec)
      residualBoundary : ResidualBoundary
      discoverResidual
        : ResidualBoundary.Resid residualBoundary
        → Set (lsuc (lsuc ℓ))
      trainingDiscoverResidual
        : ∀ p
        → discoverResidual
            (ResidualBoundary.residual residualBoundary
              (TB.KernelBridge.TransformerKernelBridge.encode
                (TB.Training.TrainingSpec.bridge spec) p))
      discoveryCoverResidual
        : ∀ {γ}
          → discoverResidual
              (ResidualBoundary.residual residualBoundary (decode γ))
          → Σ
              (TB.Ops.TransformerOps.Param
                (TB.KernelBridge.TransformerKernelBridge.ops (TB.Training.TrainingSpec.bridge spec)))
              (λ p
                → ResidualBoundary.residual residualBoundary (decode γ)
                  ≡ ResidualBoundary.residual residualBoundary
                      (TB.KernelBridge.TransformerKernelBridge.encode
                        (TB.Training.TrainingSpec.bridge spec) p))
      residualStable
        : ∀ {c d}
        → ResidualBoundary.residual residualBoundary c
            ≡ ResidualBoundary.residual residualBoundary d
        → RGStable
            (TB.Training.rgStepFromEndo
              (TB.Training.TrainingSpec.endo spec))
            c
        → RGStable
            (TB.Training.rgStepFromEndo
              (TB.Training.TrainingSpec.endo spec))
            d

    ComputeBudget : ComputeDataBudget
    ComputeBudget = computeDataBudget-from-resources resources

  optimizerFromAssumptions
    : ∀ {g} → PipelineAssumptions {g} → TB.Training.OptimizerTraining g
  optimizerFromAssumptions A =
    record
      { spec = PipelineAssumptions.spec A
      ; lossOrder = PipelineAssumptions.lossOrder A
      ; lossDecrease = PipelineAssumptions.lossMonotone A
      }

  record Pipeline {g : Scale} : Set (lsuc (lsuc (lsuc ℓ))) where
    field
      optimizer : TB.Training.OptimizerTraining g
      uir : UniversalIRCompile
      resources
        : TB.Resources.ResourceBudgets
            (TB.Training.TrainingSpec.bridge (TB.Training.OptimizerTraining.spec optimizer))

    bridge : TB.KernelBridge.TransformerKernelBridge
    bridge = TB.Training.TrainingSpec.bridge (TB.Training.OptimizerTraining.spec optimizer)

    ops : TB.Ops.TransformerOps
    ops = TB.KernelBridge.TransformerKernelBridge.ops bridge

    Param : Set ℓ
    Param = TB.Ops.TransformerOps.Param ops

    lossObsData : TB.Training.LossObservableFromData bridge
    lossObsData =
      TB.Training.TrainingSpec.lossObsData (TB.Training.OptimizerTraining.spec optimizer)

    obs : Dec → Scale
    obs = TB.Training.LossObservableFromData.obs lossObsData

    size : Code → ℕ
    size = UniversalIRCompile.size uir

    budget : Code → ℕ
    budget = TB.Resources.ResourceBudgets.compute resources

    field
      residualBoundary : ResidualBoundary
      DiscoverResidual
        : ResidualBoundary.Resid residualBoundary
        → Set (lsuc (lsuc ℓ))
      coverResidual
        : ∀ {γ}
        → DiscoverResidual
            (ResidualBoundary.residual residualBoundary (decode γ))
        → Σ Param
            (λ p
              → ResidualBoundary.residual residualBoundary (decode γ)
                ≡ ResidualBoundary.residual residualBoundary
                    (TB.KernelBridge.TransformerKernelBridge.encode bridge p))
      trainingDiscoverResidual
        : ∀ p
        → DiscoverResidual
            (ResidualBoundary.residual residualBoundary
              (TB.KernelBridge.TransformerKernelBridge.encode bridge p))

    step : RGStep g
    step = TB.Training.rgStepFromEndo (TB.Training.TrainingSpec.endo (TB.Training.OptimizerTraining.spec optimizer))

    Resid : Set ℓ
    Resid = ResidualBoundary.Resid residualBoundary

    residual : Policy → Resid
    residual = ResidualBoundary.residual residualBoundary

    Discover : Code → Set (lsuc (lsuc ℓ))
    Discover γ = DiscoverResidual (residual (decode γ))

    cover : ∀ {γ} → Discover γ → Σ Param
      (λ p → residual (decode γ)
        ≡ residual (TB.KernelBridge.TransformerKernelBridge.encode bridge p))
    cover = coverResidual

    trainingDiscover : ∀ p → Discover (TB.KernelBridge.TransformerKernelBridge.paramCode bridge p)
    trainingDiscover p =
      subst
        DiscoverResidual
        (sym
          (cong
            residual
            (TB.KernelBridge.TransformerKernelBridge.paramCode-decode bridge p)))
        (trainingDiscoverResidual p)

    policyCover : ∀ {γ} → Discover γ → Σ Param
      (λ p → residual (decode γ)
        ≡ residual (TB.KernelBridge.TransformerKernelBridge.encode bridge p))
    policyCover = cover

    field
      residualStable
        : ∀ {c d}
        → residual c ≡ residual d
        → RGStable step c
        → RGStable step d

    dim : ScalingDimension step
    dim =
      TB.Training.scalingDimensionFromLoss {s = step}
        (TB.Training.LossObservableFromData.asLossObservable lossObsData)

    stable-discovered
      : ∀ {γ} → Discover γ → RGStable step (decode γ)
    stable-discovered d =
      let p , eq = cover d
          st = TB.Training.optimizer-param-stable optimizer p
      in residualStable (sym eq) st

    scaling-discovered
      : ∀ {γ} → Discover γ → SL.ScalingBound step dim γ
    scaling-discovered d =
      SL.scalingBound-from-stable step dim (stable-discovered d)

    training-causes-scaling
      : ∀ p → SL.ScalingBound step dim
          (TB.KernelBridge.TransformerKernelBridge.paramCode bridge p)
    training-causes-scaling p =
      scaling-discovered (trainingDiscover p)

    param-scaling
      : ∀ p → SL.ScalingBound step dim
          (TB.KernelBridge.TransformerKernelBridge.paramCode bridge p)
    param-scaling p =
      let open TB.KernelBridge.TransformerKernelBridge bridge in
      let st = TB.Training.optimizer-param-stable optimizer p
          st' = CF.stable-subst (sym (paramCode-decode p)) st
      in SL.scalingBound-from-stable step dim st'

    computeDataBudget : ComputeDataBudget
    computeDataBudget = computeDataBudget-from-resources resources

    compute-limited-scaling
      : ∀ (dimCompute dimData : ScalingDimension step) {γ}
      → Discover γ
      → ComputeDataBudget.ComputeLimited computeDataBudget γ
      → SL.ScalingBound step dimCompute γ
    compute-limited-scaling dimCompute _ d _ =
      SL.scalingBound-from-stable step dimCompute (stable-discovered d)

    data-limited-scaling
      : ∀ (dimCompute dimData : ScalingDimension step) {γ}
      → Discover γ
      → ComputeDataBudget.DataLimited computeDataBudget γ
      → SL.ScalingBound step dimData γ
    data-limited-scaling _ dimData d _ =
      SL.scalingBound-from-stable step dimData (stable-discovered d)

    record ChinchillaCorollary
      (dimCompute dimData : ScalingDimension step) : Set (lsuc (lsuc ℓ)) where
      field
        computeLimited
          : ∀ {γ} → Discover γ
          → ComputeDataBudget.ComputeLimited computeDataBudget γ
          → SL.ScalingBound step dimCompute γ
        dataLimited
          : ∀ {γ} → Discover γ
          → ComputeDataBudget.DataLimited computeDataBudget γ
          → SL.ScalingBound step dimData γ

    chinchillaCorollary
      : ∀ (dimCompute dimData : ScalingDimension step)
      → ChinchillaCorollary dimCompute dimData
    chinchillaCorollary dimCompute dimData =
      record
        { computeLimited = compute-limited-scaling dimCompute dimData
        ; dataLimited = data-limited-scaling dimCompute dimData
        }

    record ScalingRegimesSummary
      (dimCompute dimData : ScalingDimension step) : Set (lsuc (lsuc ℓ)) where
      field
        discoveredScaling : ∀ {γ} → Discover γ → SL.ScalingBound step dim γ
        paramScaling : ∀ p → SL.ScalingBound step dim
          (TB.KernelBridge.TransformerKernelBridge.paramCode bridge p)
        trainingCausesScaling : ∀ p → SL.ScalingBound step dim
          (TB.KernelBridge.TransformerKernelBridge.paramCode bridge p)
        chinchillaSplit
          : ∀ {γ} → Discover γ
          → SL.ScalingBound step dimCompute γ
            ⊎ SL.ScalingBound step dimData γ

    scalingRegimes-summary
      : ∀ (dimCompute dimData : ScalingDimension step)
      → ScalingRegimesSummary dimCompute dimData
    scalingRegimes-summary dimCompute dimData =
      record
        { discoveredScaling = scaling-discovered
        ; paramScaling = param-scaling
        ; trainingCausesScaling = training-causes-scaling
        ; chinchillaSplit = split
        }
      where
        split
          : ∀ {γ} → Discover γ
          → SL.ScalingBound step dimCompute γ
            ⊎ SL.ScalingBound step dimData γ
        split {γ} d with dec≤ℕ
          (ComputeDataBudget.compute computeDataBudget γ)
          (ComputeDataBudget.dataBudget computeDataBudget γ)
        ... | inj₁ comp≤data =
          inj₁ (compute-limited-scaling dimCompute dimData d comp≤data)
        ... | inj₂ notComp≤data =
          inj₂
            (data-limited-scaling
              dimCompute
              dimData
              d
              (not≤→≥ notComp≤data))

  pipelineFromAssumptions
    : ∀ {g} → PipelineAssumptions {g} → Pipeline {g}
  pipelineFromAssumptions A =
    record
      { optimizer = optimizerFromAssumptions A
      ; uir = PipelineAssumptions.uir A
      ; resources = PipelineAssumptions.resources A
      ; residualBoundary = PipelineAssumptions.residualBoundary A
      ; DiscoverResidual = PipelineAssumptions.discoverResidual A
      ; coverResidual = PipelineAssumptions.discoveryCoverResidual A
      ; trainingDiscoverResidual = PipelineAssumptions.trainingDiscoverResidual A
      ; residualStable = PipelineAssumptions.residualStable A
      }

  record PatternParam : Set (lsuc (lsuc (lsuc ℓ))) where
    field
      obs : Dec → Scale
      size : Code → ℕ
      budget : Code → ℕ
      discover : Code → Set (lsuc (lsuc ℓ))

  module Pattern (P : PatternParam) where
    Discover : Code → Set (lsuc (lsuc ℓ))
    Discover = PatternParam.discover P

  record ParametricPipeline {g : Scale} (Θ : Set ℓ) : Set (lsuc (lsuc (lsuc ℓ))) where
    field
      base : Pipeline {g}
      params : Θ → PatternParam
      coverAt
        : ∀ θ {γ}
        → Pattern.Discover (params θ) γ
        → Σ (Pipeline.Param base)
            (λ p → decode γ
                ≡ TB.KernelBridge.TransformerKernelBridge.encode
                    (Pipeline.bridge base) p)
      trainingDiscoverAt
        : ∀ θ (p : Pipeline.Param base)
        → Pattern.Discover (params θ)
            (TB.KernelBridge.TransformerKernelBridge.paramCode
              (Pipeline.bridge base) p)

  parametric-scaling
    : ∀ {g} {Θ : Set ℓ} (P : ParametricPipeline {g} Θ)
    → ∀ θ {γ}
    → Pattern.Discover (ParametricPipeline.params P θ) γ
    → SL.ScalingBound
        (Pipeline.step (ParametricPipeline.base P))
        (Pipeline.dim (ParametricPipeline.base P))
        γ
  parametric-scaling P θ d =
    let base = ParametricPipeline.base P
        p , eq = ParametricPipeline.coverAt P θ d
        st = TB.Training.optimizer-param-stable (Pipeline.optimizer base) p
    in SL.scalingBound-from-stable
         (Pipeline.step base)
         (Pipeline.dim base)
         (CF.stable-subst (sym eq) st)

  iterate : ∀ {A : Set ℓ} → (A → A) → ℕ → A → A
  iterate f = Comp.iterate (record { Step = f ; Halts = λ _ → Topℓ })

  bootstrap-discover
    : ∀ {g} {Θ : Set ℓ} (P : ParametricPipeline {g} Θ)
    → (next : Θ → Θ)
    → (seed : Θ)
    → ∀ n (p : Pipeline.Param (ParametricPipeline.base P))
    → Pattern.Discover (ParametricPipeline.params P (iterate next n seed))
        (TB.KernelBridge.TransformerKernelBridge.paramCode
          (Pipeline.bridge (ParametricPipeline.base P)) p)
  bootstrap-discover P next seed n p =
    ParametricPipeline.trainingDiscoverAt P (iterate next n seed) p

  bootstrap-scaling
    : ∀ {g} {Θ : Set ℓ} (P : ParametricPipeline {g} Θ)
    → (next : Θ → Θ)
    → (seed : Θ)
    → ∀ n (p : Pipeline.Param (ParametricPipeline.base P))
    → SL.ScalingBound
        (Pipeline.step (ParametricPipeline.base P))
        (Pipeline.dim (ParametricPipeline.base P))
        (TB.KernelBridge.TransformerKernelBridge.paramCode
          (Pipeline.bridge (ParametricPipeline.base P)) p)
  bootstrap-scaling P next seed n p =
    parametric-scaling P (iterate next n seed)
      (bootstrap-discover P next seed n p)


  scalingRegimes-theorem
    : ∀ {g} (A : PipelineAssumptions {g})
    → (dimCompute dimData
        : RG.ScalingDimension
            (Pipeline.step (pipelineFromAssumptions A)))
    → Pipeline.ScalingRegimesSummary
        (pipelineFromAssumptions A) dimCompute dimData
  scalingRegimes-theorem A dimCompute dimData =
    Pipeline.scalingRegimes-summary
      (pipelineFromAssumptions A) dimCompute dimData
