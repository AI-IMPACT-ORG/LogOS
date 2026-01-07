{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Arguments.TransformerScalingPipeline where

open import LogOS.Prelude

open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.NatLog2 using () renaming (mul to mulℕ)

infix 4 _≢_
_≢_ : ∀ {ℓX : Level} {X : Set ℓX} → X → X → Set ℓX
_≢_ {ℓX = ℓX} x y = x ≡ y → ⊥ {ℓ = ℓX}

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary; ConPoset)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel.Graded using (GradedKernel)

import LogOS.Packs.Agents.Arguments.TransformerBridge as TransformerBridge
import LogOS.Packs.Agents.Arguments.TransformerKolmogorovScaling as TransformerKolmogorovScaling
import LogOS.Packs.Agents.Learning.RGFlow as RGFlow
import LogOS.Packs.Agents.Arguments.ScalingLaws as ScalingLaws
import LogOS.Packs.Agents.Arguments.TransformerFormalization as TransformerFormalization

-- Unified, LogOS-aligned pipeline:
-- - loss dynamics define stability at the RG level,
-- - stability yields scaling bounds,
-- - discovery selects the observable fragment,
-- - resource budgets split compute/data regimes.

module For
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO)
            (BulkBoundary.bnd (GradedKernel.BB K)))
  where

  module TB = TransformerBridge.For K ωCPO
  module TK = TransformerKolmogorovScaling.For K ωCPO
  module RG = RGFlow.For K ωCPO
  module SL = ScalingLaws.For K ωCPO
  module TF = TransformerFormalization.For K ωCPO

  open GradedKernel K using (Code; decode)
  open QAdapter Q using (Scale; _≤s_)
  open RG using (Policy; RGStep; RGStable; ScalingDimension; applyRG)

  Dec : Set ℓ
  Dec = ConPoset.Con (BulkBoundary.bnd (GradedKernel.BB K))

  LossMonotone : ∀ {g} (s : RGStep g) → (Policy → Scale) → Set ℓ
  LossMonotone s obs =
    ∀ c → _≤s_ (obs (applyRG s c)) (obs c)

  record LossDynamics {g : Scale} (s : RGStep g) : Set (lsuc (lsuc ℓ)) where
    field
      dim : ScalingDimension s
      order : TB.LossOrder (ScalingDimension.obs dim)
      decrease : LossMonotone s (ScalingDimension.obs dim)

  loss-stable
    : ∀ {g} {s : RGStep g} (L : LossDynamics s) (c : Policy)
    → RGStable s c
  loss-stable L c =
    TB.lossDecrease-stable
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
    : ∀ {g} {s : RGStep g} {B : TB.TransformerKernelBridge}
    → (L : TB.NextTokenLossObservableFromData B)
    → TB.LossOrder (TB.NextTokenLossObservableFromData.obs L)
    → LossMonotone s (TB.NextTokenLossObservableFromData.obs L)
    → LossDynamics s
  nextTokenLossDynamics {s = s} L order dec =
    let L' = TB.NextTokenLossObservableFromData.asLossObservableFromData L
        dim = TB.scalingDimensionFromLoss {s = s}
                (TB.LossObservableFromData.asLossObservable L')
    in record
      { dim = dim
      ; order = order
      ; decrease = dec
      }

  record PipelineAssumptions {g : Scale} : Set (lsuc (lsuc ℓ)) where
    field
      spec : TB.TrainingSpec g
      lossObsData : TB.LossObservableFromData (TB.TrainingSpec.bridge spec)
      lossOrder : TB.LossOrder (TB.LossObservableFromData.obs lossObsData)
      lossMonotone
        : ∀ p
        → _≤s_
            (TB.lossParam (TB.LossObservableFromData.lossData lossObsData)
              (TB.TrainingSpec.trainParam spec p))
            (TB.lossParam (TB.LossObservableFromData.lossData lossObsData) p)
      uir : TK.UniversalIRCompile
      resources
        : TB.ResourceBudgets (TB.TrainingSpec.bridge spec)
      trainingDiscover
        : ∀ p
        → TK.Obs.DiscoverCode
            (TB.LossObservableFromData.obs lossObsData)
            (TK.UniversalIRCompile.size uir)
            (TK.CodeBudget.B (TK.codeBudget-from-resources resources))
            (TB.TransformerKernelBridge.paramCode (TB.TrainingSpec.bridge spec) p)
      discoveryCover
        : ∀ {γ}
          → TK.Obs.DiscoverCode
              (TB.LossObservableFromData.obs lossObsData)
              (TK.UniversalIRCompile.size uir)
              (TK.CodeBudget.B (TK.codeBudget-from-resources resources))
              γ
          → Σ
              (TB.TransformerOps.Param
                (TB.TransformerKernelBridge.ops (TB.TrainingSpec.bridge spec)))
              (λ p → decode γ ≡ TB.TransformerKernelBridge.encode
                        (TB.TrainingSpec.bridge spec) p)

    ComputeBudget : TK.ComputeDataBudget
    ComputeBudget = TK.computeDataBudget-from-resources resources

  optimizerFromAssumptions
    : ∀ {g} → PipelineAssumptions {g} → TB.OptimizerTraining g
  optimizerFromAssumptions A =
    record
      { spec = PipelineAssumptions.spec A
      ; lossObsData = PipelineAssumptions.lossObsData A
      ; lossOrder = PipelineAssumptions.lossOrder A
      ; lossDecrease = PipelineAssumptions.lossMonotone A
      }

  record Pipeline {g : Scale} : Set (lsuc (lsuc ℓ)) where
    field
      optimizer : TB.OptimizerTraining g
      uir : TK.UniversalIRCompile
      resources
        : TB.ResourceBudgets
            (TB.TrainingSpec.bridge (TB.OptimizerTraining.spec optimizer))

    bridge : TB.TransformerKernelBridge
    bridge = TB.TrainingSpec.bridge (TB.OptimizerTraining.spec optimizer)

    ops : TB.TransformerOps
    ops = TB.TransformerKernelBridge.ops bridge

    Param : Set ℓ
    Param = TB.TransformerOps.Param ops

    lossObsData : TB.LossObservableFromData bridge
    lossObsData = TB.OptimizerTraining.lossObsData optimizer

    obs : Dec → Scale
    obs = TB.LossObservableFromData.obs lossObsData

    size : Code → ℕ
    size = TK.UniversalIRCompile.size uir

    budget : Code → ℕ
    budget = TB.ResourceBudgets.compute resources

    module Obs = TK.Obs obs size budget

    Discover : Code → Set (lsuc (lsuc ℓ))
    Discover = Obs.DiscoverCode

    field
      cover : ∀ {γ} → Discover γ → Σ Param
        (λ p → decode γ ≡ TB.TransformerKernelBridge.encode bridge p)
      trainingDiscover : ∀ p → Discover (TB.TransformerKernelBridge.paramCode bridge p)

    policyCover : ∀ {γ} → Discover γ → Σ Param
      (λ p → decode γ ≡ TB.TransformerKernelBridge.encode bridge p)
    policyCover = cover

    step : RGStep g
    step = TB.rgStepFromEndo (TB.TrainingSpec.endo (TB.OptimizerTraining.spec optimizer))

    dim : ScalingDimension step
    dim =
      TB.scalingDimensionFromLoss {s = step}
        (TB.LossObservableFromData.asLossObservable lossObsData)

    stable-discovered
      : ∀ {γ} → Discover γ → RGStable step (decode γ)
    stable-discovered d =
      let p , eq = cover d
          st = TB.optimizer-param-stable optimizer p
      in TF.stable-subst (sym eq) st

    scaling-discovered
      : ∀ {γ} → Discover γ → SL.ScalingBound step dim γ
    scaling-discovered d =
      SL.scalingBound-from-stable step dim (stable-discovered d)

    training-causes-scaling
      : ∀ p → SL.ScalingBound step dim
          (TB.TransformerKernelBridge.paramCode bridge p)
    training-causes-scaling p =
      scaling-discovered (trainingDiscover p)

    param-scaling
      : ∀ p → SL.ScalingBound step dim
          (TB.TransformerKernelBridge.paramCode bridge p)
    param-scaling p =
      let open TB.TransformerKernelBridge bridge in
      let st = TB.optimizer-param-stable optimizer p
          st' = TF.stable-subst (sym (paramCode-decode p)) st
      in SL.scalingBound-from-stable step dim st'

    codeBudget : TK.CodeBudget
    codeBudget = TK.codeBudget-from-resources resources

    computeDataBudget : TK.ComputeDataBudget
    computeDataBudget = TK.computeDataBudget-from-resources resources

    kolmogorovBridge : TK.KolmogorovBridge {g}
    kolmogorovBridge =
      record
        { train = TB.OptimizerTraining.spec optimizer
        ; uir = uir
        ; budget = codeBudget
        ; lossObs = lossObsData
        ; stable = stable-discovered
        }

    twoRegimeBridge
      : TK.BudgetPhase (TK.CodeBudget.B codeBudget)
      → ScalingDimension step
      → ScalingDimension step
      → TK.TwoRegimeBridge {g}
    twoRegimeBridge phase dimLow dimHigh =
      record
        { base = kolmogorovBridge
        ; phase = phase
        ; dimLow = dimLow
        ; dimHigh = dimHigh
        }

    chinchillaBridge
      : ScalingDimension step
      → ScalingDimension step
      → TK.ChinchillaBridge {g}
    chinchillaBridge dimCompute dimData =
      record
        { base = kolmogorovBridge
        ; budgets = computeDataBudget
        ; dimCompute = dimCompute
        ; dimData = dimData
        }

    record ChinchillaCorollary
      (dimCompute dimData : ScalingDimension step) : Set (lsuc (lsuc ℓ)) where
      field
        computeLimited
          : ∀ {γ} → Discover γ
          → TK.ComputeDataBudget.ComputeLimited computeDataBudget γ
          → SL.ScalingBound step dimCompute γ
        dataLimited
          : ∀ {γ} → Discover γ
          → TK.ComputeDataBudget.DataLimited computeDataBudget γ
          → SL.ScalingBound step dimData γ

    chinchillaCorollary
      : ∀ (dimCompute dimData : ScalingDimension step)
      → ChinchillaCorollary dimCompute dimData
    chinchillaCorollary dimCompute dimData =
      let B = chinchillaBridge dimCompute dimData in
      record
        { computeLimited = TK.compute-limited-scaling B
        ; dataLimited = TK.data-limited-scaling B
        }

    record ScalingRegimesSummary
      (dimCompute dimData : ScalingDimension step) : Set (lsuc (lsuc ℓ)) where
      field
        discoveredScaling : ∀ {γ} → Discover γ → SL.ScalingBound step dim γ
        paramScaling : ∀ p → SL.ScalingBound step dim
          (TB.TransformerKernelBridge.paramCode bridge p)
        trainingCausesScaling : ∀ p → SL.ScalingBound step dim
          (TB.TransformerKernelBridge.paramCode bridge p)
        chinchillaSplit
          : ∀ {γ} → Discover γ
          → SL.ScalingBound step dimCompute γ
            ⊎ SL.ScalingBound step dimData γ

    scalingRegimes-summary
      : ∀ (dimCompute dimData : ScalingDimension step)
      → ScalingRegimesSummary dimCompute dimData
    scalingRegimes-summary dimCompute dimData =
      let B = chinchillaBridge dimCompute dimData in
      record
        { discoveredScaling = scaling-discovered
        ; paramScaling = param-scaling
        ; trainingCausesScaling = training-causes-scaling
        ; chinchillaSplit = TK.chinchilla-compare B
        }

  pipelineFromAssumptions
    : ∀ {g} → PipelineAssumptions {g} → Pipeline {g}
  pipelineFromAssumptions A =
    record
      { optimizer = optimizerFromAssumptions A
      ; uir = PipelineAssumptions.uir A
      ; resources = PipelineAssumptions.resources A
      ; cover = PipelineAssumptions.discoveryCover A
      ; trainingDiscover = PipelineAssumptions.trainingDiscover A
      }

  record PatternParam : Set (lsuc (lsuc ℓ)) where
    field
      obs : Dec → Scale
      size : Code → ℕ
      budget : Code → ℕ

  module Pattern (P : PatternParam) where
    module Obs = TK.Obs (PatternParam.obs P)
                        (PatternParam.size P)
                        (PatternParam.budget P)
    Discover : Code → Set (lsuc (lsuc ℓ))
    Discover = Obs.DiscoverCode

  record ParametricPipeline {g : Scale} (Θ : Set ℓ) : Set (lsuc (lsuc ℓ)) where
    field
      base : Pipeline {g}
      params : Θ → PatternParam
      coverAt
        : ∀ θ {γ}
        → Pattern.Discover (params θ) γ
        → Σ (Pipeline.Param base)
            (λ p → decode γ
                ≡ TB.TransformerKernelBridge.encode
                    (Pipeline.bridge base) p)
      trainingDiscoverAt
        : ∀ θ (p : Pipeline.Param base)
        → Pattern.Discover (params θ)
            (TB.TransformerKernelBridge.paramCode
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
        st = TB.optimizer-param-stable (Pipeline.optimizer base) p
    in SL.scalingBound-from-stable
         (Pipeline.step base)
         (Pipeline.dim base)
         (TF.stable-subst (sym eq) st)

  iterate : ∀ {A : Set ℓ} → (A → A) → ℕ → A → A
  iterate f zero a = a
  iterate f (suc n) a = iterate f n (f a)

  bootstrap-discover
    : ∀ {g} {Θ : Set ℓ} (P : ParametricPipeline {g} Θ)
    → (next : Θ → Θ)
    → (seed : Θ)
    → ∀ n (p : Pipeline.Param (ParametricPipeline.base P))
    → Pattern.Discover (ParametricPipeline.params P (iterate next n seed))
        (TB.TransformerKernelBridge.paramCode
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
        (TB.TransformerKernelBridge.paramCode
          (Pipeline.bridge (ParametricPipeline.base P)) p)
  bootstrap-scaling P next seed n p =
    parametric-scaling P (iterate next n seed)
      (bootstrap-discover P next seed n p)

  record Exponent : Set where
    field
      num : ℕ
      den : ℕ
      den≢0 : den ≢ 0

  nonZeroSuc : ∀ n → suc n ≢ 0
  nonZeroSuc _ ()

  nonZeroMul : ∀ {a b} → a ≢ 0 → b ≢ 0 → a * b ≢ 0
  nonZeroMul {zero} a≢0 _ = ⊥-elim (a≢0 refl)
  nonZeroMul {suc _} {zero} _ b≢0 = ⊥-elim (b≢0 refl)
  nonZeroMul {suc _} {suc _} _ _ = λ ()

  nonZeroAddLeft : ∀ {a b} → a ≢ 0 → a + b ≢ 0
  nonZeroAddLeft {zero} a≢0 = ⊥-elim (a≢0 refl)
  nonZeroAddLeft {suc _} _ = λ ()

  nonZeroOne : 1 ≢ 0
  nonZeroOne = nonZeroSuc zero

  ratio : (num den : ℕ) → den ≢ 0 → Exponent
  ratio num den den≢0 = record { num = num ; den = den ; den≢0 = den≢0 }

  record ResourcePrinciple : Set (lsuc ℓ) where
    field
      alpha : ℕ
      beta : ℕ
      total≢0 : alpha + beta ≢ 0

    total : ℕ
    total = alpha + beta

    computeExponent : Exponent
    computeExponent = ratio beta total total≢0

    dataExponent : Exponent
    dataExponent = ratio alpha total total≢0

    lossExponent : Exponent
    lossExponent = ratio (mulℕ alpha beta) total total≢0

  record ResourceExponents : Set (lsuc ℓ) where
    field
      compute : Exponent
      dataExp : Exponent
      loss : Exponent

  deriveResourceExponents : ResourcePrinciple → ResourceExponents
  deriveResourceExponents R =
    record
      { compute = ResourcePrinciple.computeExponent R
      ; dataExp = ResourcePrinciple.dataExponent R
      ; loss = ResourcePrinciple.lossExponent R
      }

  toyUnitPrinciple : ResourcePrinciple
  toyUnitPrinciple =
    record
      { alpha = 1
      ; beta = 1
      ; total≢0 = nonZeroSuc 1
      }

  toyUnitComputeExponent
    : ResourcePrinciple.computeExponent toyUnitPrinciple
      ≡ ratio 1 2 (nonZeroSuc 1)
  toyUnitComputeExponent = refl

  toyUnitDataExponent
    : ResourcePrinciple.dataExponent toyUnitPrinciple
      ≡ ratio 1 2 (nonZeroSuc 1)
  toyUnitDataExponent = refl

  toyUnitLossExponent
    : ResourcePrinciple.lossExponent toyUnitPrinciple
      ≡ ratio 1 2 (nonZeroSuc 1)
  toyUnitLossExponent = refl

  expAdd : Exponent → Exponent → Exponent
  expAdd e₁ e₂ =
    ratio
      (Exponent.num e₁ * Exponent.den e₂ + Exponent.num e₂ * Exponent.den e₁)
      (Exponent.den e₁ * Exponent.den e₂)
      (nonZeroMul (Exponent.den≢0 e₁) (Exponent.den≢0 e₂))

  expMul : Exponent → Exponent → Exponent
  expMul e₁ e₂ =
    ratio
      (Exponent.num e₁ * Exponent.num e₂)
      (Exponent.den e₁ * Exponent.den e₂)
      (nonZeroMul (Exponent.den≢0 e₁) (Exponent.den≢0 e₂))

  expRecip : (e : Exponent) → Exponent.num e ≢ 0 → Exponent
  expRecip e num≢0 = ratio (Exponent.den e) (Exponent.num e) num≢0

  expDiv : (e₁ e₂ : Exponent) → Exponent.num e₂ ≢ 0 → Exponent
  expDiv e₁ e₂ num≢0 = expMul e₁ (expRecip e₂ num≢0)

  record AnomalousDimension : Set where
    field
      classical : Exponent
      anomaly : Exponent
      observed : Exponent
      relation : observed ≡ expAdd classical anomaly

  record BootstrapConstraint : Set (lsuc ℓ) where
    field
      step : Exponent → Exponent
      fixed : Exponent
      fixedPoint : fixed ≡ step fixed

  bootstrap-anomalous
    : ∀ (P : ResourcePrinciple) (B : BootstrapConstraint) (Δ : Exponent)
    → BootstrapConstraint.fixed B
      ≡ expAdd (ResourcePrinciple.lossExponent P) Δ
    → AnomalousDimension
  bootstrap-anomalous P B Δ rel =
    record
      { classical = ResourcePrinciple.lossExponent P
      ; anomaly = Δ
      ; observed = BootstrapConstraint.fixed B
      ; relation = rel
      }

  record ResourcePrincipleRational : Set (lsuc ℓ) where
    field
      alphaExp : Exponent
      betaExp : Exponent
      totalNum≢0 : Exponent.num (expAdd alphaExp betaExp) ≢ 0

    totalExp : Exponent
    totalExp = expAdd alphaExp betaExp

    computeExponent : Exponent
    computeExponent = expDiv betaExp totalExp totalNum≢0

    dataExponent : Exponent
    dataExponent = expDiv alphaExp totalExp totalNum≢0

    lossExponent : Exponent
    lossExponent = expDiv (expMul alphaExp betaExp) totalExp totalNum≢0

  deriveResourceExponentsRational : ResourcePrincipleRational → ResourceExponents
  deriveResourceExponentsRational R =
    record
      { compute = ResourcePrincipleRational.computeExponent R
      ; dataExp = ResourcePrincipleRational.dataExponent R
      ; loss = ResourcePrincipleRational.lossExponent R
      }

  expNat : ℕ → Exponent
  expNat n = ratio n 1 nonZeroOne

  record SymmetricPrinciple : Set (lsuc ℓ) where
    field
      alphaExp : Exponent
      totalNum≢0 : Exponent.num (expAdd alphaExp alphaExp) ≢ 0

    principle : ResourcePrincipleRational
    principle =
      record
        { alphaExp = alphaExp
        ; betaExp = alphaExp
        ; totalNum≢0 = totalNum≢0
        }

    exponents : ResourceExponents
    exponents = deriveResourceExponentsRational principle

  symmetric-compute=data
    : ∀ (S : SymmetricPrinciple)
    → ResourceExponents.compute (SymmetricPrinciple.exponents S)
      ≡ ResourceExponents.dataExp (SymmetricPrinciple.exponents S)
  symmetric-compute=data S = refl

  cleanPrinciple : ResourcePrincipleRational
  cleanPrinciple =
    record
      { alphaExp = expNat 1
      ; betaExp = expNat 1
      ; totalNum≢0 = nonZeroSuc 1
      }

  cleanExponents : ResourceExponents
  cleanExponents = deriveResourceExponentsRational cleanPrinciple

  symAlphaFromLoss : Exponent → Exponent
  symAlphaFromLoss loss = expMul loss (expNat 2)

  symAlphaNumNonZero
    : ∀ loss → Exponent.num loss ≢ 0
    → Exponent.num (symAlphaFromLoss loss) ≢ 0
  symAlphaNumNonZero _ lossNum≢0 =
    nonZeroMul lossNum≢0 (nonZeroSuc 1)

  symTotalNumNonZero
    : ∀ loss → Exponent.num loss ≢ 0
    → Exponent.num (expAdd (symAlphaFromLoss loss) (symAlphaFromLoss loss)) ≢ 0
  symTotalNumNonZero loss lossNum≢0 =
    let alpha = symAlphaFromLoss loss
        alphaNum≢0 = symAlphaNumNonZero loss lossNum≢0
        termNonZero = nonZeroMul alphaNum≢0 (Exponent.den≢0 alpha)
    in nonZeroAddLeft termNonZero

  symPrincipleFromLoss
    : (loss : Exponent)
    → Exponent.num loss ≢ 0
    → ResourcePrincipleRational
  symPrincipleFromLoss loss lossNum≢0 =
    record
      { alphaExp = symAlphaFromLoss loss
      ; betaExp = symAlphaFromLoss loss
      ; totalNum≢0 = symTotalNumNonZero loss lossNum≢0
      }

  symExponentsFromLoss
    : (loss : Exponent)
    → Exponent.num loss ≢ 0
    → ResourceExponents
  symExponentsFromLoss loss lossNum≢0 =
    deriveResourceExponentsRational (symPrincipleFromLoss loss lossNum≢0)

  chinchillaLossExp : Exponent
  chinchillaLossExp = ratio 1 20 (nonZeroSuc 19)

  chinchillaPrinciple : ResourcePrincipleRational
  chinchillaPrinciple =
    symPrincipleFromLoss chinchillaLossExp nonZeroOne

  chinchillaAlpha : Exponent
  chinchillaAlpha = ResourcePrincipleRational.alphaExp chinchillaPrinciple

  chinchillaBeta : Exponent
  chinchillaBeta = ResourcePrincipleRational.betaExp chinchillaPrinciple

  chinchillaExponents : ResourceExponents
  chinchillaExponents = deriveResourceExponentsRational chinchillaPrinciple

  alphaExp : ResourcePrinciple → Exponent
  alphaExp R = expNat (ResourcePrinciple.alpha R)

  betaExp : ResourcePrinciple → Exponent
  betaExp R = expNat (ResourcePrinciple.beta R)

  record PowerLawOps : Set (lsuc (lsuc ℓ)) where
    field
      R : Set ℓ
      0# : R
      1# : R
      add : R → R → R
      mul : R → R → R
      inv : R → R
      pow : R → Exponent → R

  record OrderedPowerLawOps : Set (lsuc (lsuc ℓ)) where
    field
      ops : PowerLawOps
      _≤r_ : PowerLawOps.R ops → PowerLawOps.R ops → Set ℓ
      ≤r-refl : ∀ {x} → _≤r_ x x
      ≤r-trans : ∀ {x y z} → _≤r_ x y → _≤r_ y z → _≤r_ x z
      add-mono
        : ∀ {a b c d}
        → _≤r_ a b
        → _≤r_ c d
        → _≤r_ (PowerLawOps.add ops a c) (PowerLawOps.add ops b d)
      mul-mono
        : ∀ {a b c d}
        → _≤r_ a b
        → _≤r_ c d
        → _≤r_ (PowerLawOps.mul ops a c) (PowerLawOps.mul ops b d)
      pow-mono
        : ∀ {a b} → _≤r_ a b → ∀ {e}
        → _≤r_ (PowerLawOps.pow ops a e) (PowerLawOps.pow ops b e)

    infix 4 _≤r_

  record AddSwap (O : OrderedPowerLawOps) : Set (lsuc ℓ) where
    open OrderedPowerLawOps O
    field
      add-swap
        : ∀ a b
        → _≤r_
            (PowerLawOps.add ops a b)
            (PowerLawOps.add ops b a)

  powNeg : ∀ {ops : PowerLawOps} → PowerLawOps.R ops → Exponent → PowerLawOps.R ops
  powNeg {ops} x e =
    let open PowerLawOps ops in
    inv (pow x e)

  record Homogeneous (ops : PowerLawOps) (exp : Exponent)
                     (f : PowerLawOps.R ops → PowerLawOps.R ops)
                     : Set (lsuc (lsuc ℓ)) where
    field
      scale
        : ∀ k x
        → f (PowerLawOps.mul ops k x)
          ≡ PowerLawOps.mul ops (powNeg {ops} k exp) (f x)

  record PowerLawAxiom (ops : PowerLawOps) : Set (lsuc (lsuc ℓ)) where
    field
      characterize
        : ∀ {f exp}
        → Homogeneous ops exp f
        → Σ (PowerLawOps.R ops)
            (λ A → ∀ x → f x ≡ PowerLawOps.mul ops A (powNeg {ops} x exp))

  record PowerLawWitness (ops : PowerLawOps) (exp : Exponent)
                         (f : PowerLawOps.R ops → PowerLawOps.R ops)
                         : Set (lsuc (lsuc ℓ)) where
    field
      A : PowerLawOps.R ops
      form : ∀ x → f x ≡ PowerLawOps.mul ops A (powNeg {ops} x exp)

  record PowerLawBand (O : OrderedPowerLawOps) (exp : Exponent)
                      (f : PowerLawOps.R (OrderedPowerLawOps.ops O)
                           → PowerLawOps.R (OrderedPowerLawOps.ops O))
                      : Set (lsuc (lsuc ℓ)) where
    field
      Alo : PowerLawOps.R (OrderedPowerLawOps.ops O)
      Ahi : PowerLawOps.R (OrderedPowerLawOps.ops O)
      lower
        : ∀ x
        → OrderedPowerLawOps._≤r_ O
            (PowerLawOps.mul (OrderedPowerLawOps.ops O) Alo
              (powNeg {ops = OrderedPowerLawOps.ops O} x exp))
            (f x)
      upper
        : ∀ x
        → OrderedPowerLawOps._≤r_ O
            (f x)
            (PowerLawOps.mul (OrderedPowerLawOps.ops O) Ahi
              (powNeg {ops = OrderedPowerLawOps.ops O} x exp))

  record SeparableHomogeneousLoss (ops : PowerLawOps) : Set (lsuc (lsuc ℓ)) where
    field
      principle : ResourcePrinciple
      loss : PowerLawOps.R ops → PowerLawOps.R ops → PowerLawOps.R ops
      Linf : PowerLawOps.R ops
      f : PowerLawOps.R ops → PowerLawOps.R ops
      g : PowerLawOps.R ops → PowerLawOps.R ops
      sep : ∀ N D → loss N D
            ≡ PowerLawOps.add ops Linf
                (PowerLawOps.add ops (f N) (g D))
      homF : Homogeneous ops (alphaExp principle) f
      homG : Homogeneous ops (betaExp principle) g

  record SeparablePowerLawLoss (ops : PowerLawOps) : Set (lsuc (lsuc ℓ)) where
    field
      principle : ResourcePrinciple
      loss : PowerLawOps.R ops → PowerLawOps.R ops → PowerLawOps.R ops
      Linf : PowerLawOps.R ops
      f : PowerLawOps.R ops → PowerLawOps.R ops
      g : PowerLawOps.R ops → PowerLawOps.R ops
      sep : ∀ N D → loss N D
            ≡ PowerLawOps.add ops Linf
                (PowerLawOps.add ops (f N) (g D))
      powF : PowerLawWitness ops (alphaExp principle) f
      powG : PowerLawWitness ops (betaExp principle) g

  record SeparablePowerLawBandLoss (O : OrderedPowerLawOps) : Set (lsuc (lsuc ℓ)) where
    field
      principle : ResourcePrinciple
      loss : PowerLawOps.R (OrderedPowerLawOps.ops O)
             → PowerLawOps.R (OrderedPowerLawOps.ops O)
             → PowerLawOps.R (OrderedPowerLawOps.ops O)
      Linf : PowerLawOps.R (OrderedPowerLawOps.ops O)
      f : PowerLawOps.R (OrderedPowerLawOps.ops O)
          → PowerLawOps.R (OrderedPowerLawOps.ops O)
      g : PowerLawOps.R (OrderedPowerLawOps.ops O)
          → PowerLawOps.R (OrderedPowerLawOps.ops O)
      sep : ∀ N D → loss N D
            ≡ PowerLawOps.add (OrderedPowerLawOps.ops O) Linf
                (PowerLawOps.add (OrderedPowerLawOps.ops O) (f N) (g D))
      bandF : PowerLawBand O (alphaExp principle) f
      bandG : PowerLawBand O (betaExp principle) g

  record KaplanForm (ops : PowerLawOps) (P : ResourcePrinciple) : Set (lsuc (lsuc ℓ)) where
    field
      loss : PowerLawOps.R ops → PowerLawOps.R ops → PowerLawOps.R ops
      Linf : PowerLawOps.R ops
      A : PowerLawOps.R ops
      B : PowerLawOps.R ops
      form
        : ∀ N D → loss N D
          ≡ PowerLawOps.add ops Linf
              (PowerLawOps.add ops
                (PowerLawOps.mul ops A (powNeg {ops} N (alphaExp P)))
                (PowerLawOps.mul ops B (powNeg {ops} D (betaExp P))))

  record KaplanBounds (O : OrderedPowerLawOps) (P : ResourcePrinciple)
    : Set (lsuc (lsuc ℓ)) where
    field
      loss : PowerLawOps.R (OrderedPowerLawOps.ops O)
             → PowerLawOps.R (OrderedPowerLawOps.ops O)
             → PowerLawOps.R (OrderedPowerLawOps.ops O)
      Linf : PowerLawOps.R (OrderedPowerLawOps.ops O)
      Alo : PowerLawOps.R (OrderedPowerLawOps.ops O)
      Ahi : PowerLawOps.R (OrderedPowerLawOps.ops O)
      Blo : PowerLawOps.R (OrderedPowerLawOps.ops O)
      Bhi : PowerLawOps.R (OrderedPowerLawOps.ops O)
      lower
        : ∀ N D
        → OrderedPowerLawOps._≤r_ O
            (PowerLawOps.add (OrderedPowerLawOps.ops O) Linf
              (PowerLawOps.add (OrderedPowerLawOps.ops O)
                (PowerLawOps.mul (OrderedPowerLawOps.ops O) Alo
                  (powNeg {ops = OrderedPowerLawOps.ops O} N (alphaExp P)))
                (PowerLawOps.mul (OrderedPowerLawOps.ops O) Blo
                  (powNeg {ops = OrderedPowerLawOps.ops O} D (betaExp P)))))
            (loss N D)
      upper
        : ∀ N D
        → OrderedPowerLawOps._≤r_ O
            (loss N D)
            (PowerLawOps.add (OrderedPowerLawOps.ops O) Linf
              (PowerLawOps.add (OrderedPowerLawOps.ops O)
                (PowerLawOps.mul (OrderedPowerLawOps.ops O) Ahi
                  (powNeg {ops = OrderedPowerLawOps.ops O} N (alphaExp P)))
                (PowerLawOps.mul (OrderedPowerLawOps.ops O) Bhi
                  (powNeg {ops = OrderedPowerLawOps.ops O} D (betaExp P)))))

  record ExponentSliceBounds (O : OrderedPowerLawOps) (exp : Exponent)
                             (f : PowerLawOps.R (OrderedPowerLawOps.ops O)
                                  → PowerLawOps.R (OrderedPowerLawOps.ops O))
                             : Set (lsuc (lsuc ℓ)) where
    field
      Linf : PowerLawOps.R (OrderedPowerLawOps.ops O)
      Clo : PowerLawOps.R (OrderedPowerLawOps.ops O)
      Chi : PowerLawOps.R (OrderedPowerLawOps.ops O)
      Alo : PowerLawOps.R (OrderedPowerLawOps.ops O)
      Ahi : PowerLawOps.R (OrderedPowerLawOps.ops O)
      lower
        : ∀ x
        → OrderedPowerLawOps._≤r_ O
            (PowerLawOps.add (OrderedPowerLawOps.ops O) Linf
              (PowerLawOps.add (OrderedPowerLawOps.ops O)
                (PowerLawOps.mul (OrderedPowerLawOps.ops O) Alo
                  (powNeg {ops = OrderedPowerLawOps.ops O} x exp))
                Clo))
            (f x)
      upper
        : ∀ x
        → OrderedPowerLawOps._≤r_ O
            (f x)
            (PowerLawOps.add (OrderedPowerLawOps.ops O) Linf
              (PowerLawOps.add (OrderedPowerLawOps.ops O)
                (PowerLawOps.mul (OrderedPowerLawOps.ops O) Ahi
                  (powNeg {ops = OrderedPowerLawOps.ops O} x exp))
                Chi))

  deriveKaplanForm
    : ∀ {ops : PowerLawOps}
    → (ax : PowerLawAxiom ops)
    → (L : SeparableHomogeneousLoss ops)
    → KaplanForm ops (SeparableHomogeneousLoss.principle L)
  deriveKaplanForm {ops} ax L =
    let open PowerLawOps ops in
    let P = SeparableHomogeneousLoss.principle L
        loss = SeparableHomogeneousLoss.loss L
        Linf = SeparableHomogeneousLoss.Linf L
        f = SeparableHomogeneousLoss.f L
        g = SeparableHomogeneousLoss.g L
        sep = SeparableHomogeneousLoss.sep L
        homF = SeparableHomogeneousLoss.homF L
        homG = SeparableHomogeneousLoss.homG L
        A = proj₁ (PowerLawAxiom.characterize ax homF)
        Af = proj₂ (PowerLawAxiom.characterize ax homF)
        B = proj₁ (PowerLawAxiom.characterize ax homG)
        Bg = proj₂ (PowerLawAxiom.characterize ax homG)
    in
    record
      { loss = loss
      ; Linf = Linf
      ; A = A
      ; B = B
      ; form = λ N D →
          trans
            (sep N D)
            (cong
              (PowerLawOps.add ops Linf)
              (cong₂
                (PowerLawOps.add ops)
                (Af N)
                (Bg D)))
      }

  deriveKaplanBounds
    : ∀ {O : OrderedPowerLawOps}
    → (L : SeparablePowerLawBandLoss O)
    → KaplanBounds O (SeparablePowerLawBandLoss.principle L)
  deriveKaplanBounds {O} L =
    let open OrderedPowerLawOps O in
    let ops = OrderedPowerLawOps.ops O
        P = SeparablePowerLawBandLoss.principle L
        loss = SeparablePowerLawBandLoss.loss L
        Linf = SeparablePowerLawBandLoss.Linf L
        f = SeparablePowerLawBandLoss.f L
        g = SeparablePowerLawBandLoss.g L
        sep = SeparablePowerLawBandLoss.sep L
        bandF = SeparablePowerLawBandLoss.bandF L
        bandG = SeparablePowerLawBandLoss.bandG L
        Alo = PowerLawBand.Alo bandF
        Ahi = PowerLawBand.Ahi bandF
        Blo = PowerLawBand.Alo bandG
        Bhi = PowerLawBand.Ahi bandG
        lowerF = PowerLawBand.lower bandF
        upperF = PowerLawBand.upper bandF
        lowerG = PowerLawBand.lower bandG
        upperG = PowerLawBand.upper bandG
    in
    record
      { loss = loss
      ; Linf = Linf
      ; Alo = Alo
      ; Ahi = Ahi
      ; Blo = Blo
      ; Bhi = Bhi
      ; lower = λ N D →
          let bound =
                add-mono
                  (≤r-refl {x = Linf})
                  (add-mono (lowerF N) (lowerG D))
          in subst
              (λ x → _≤r_
                (PowerLawOps.add ops Linf
                  (PowerLawOps.add ops
                    (PowerLawOps.mul ops Alo
                      (powNeg {ops = ops} N (alphaExp P)))
                    (PowerLawOps.mul ops Blo
                      (powNeg {ops = ops} D (betaExp P)))))
                x)
              (sym (sep N D))
              bound
      ; upper = λ N D →
          let bound =
                add-mono
                  (≤r-refl {x = Linf})
                  (add-mono (upperF N) (upperG D))
          in subst
              (λ x → _≤r_ x
                (PowerLawOps.add ops Linf
                  (PowerLawOps.add ops
                    (PowerLawOps.mul ops Ahi
                      (powNeg {ops = ops} N (alphaExp P)))
                    (PowerLawOps.mul ops Bhi
                      (powNeg {ops = ops} D (betaExp P))))))
              (sym (sep N D))
              bound
      }

  kaplanBounds-sliceN
    : ∀ {O : OrderedPowerLawOps} {P : ResourcePrinciple}
    → (K : KaplanBounds O P)
    → (D : PowerLawOps.R (OrderedPowerLawOps.ops O))
    → ExponentSliceBounds O (alphaExp P)
        (λ N → KaplanBounds.loss K N D)
  kaplanBounds-sliceN {O} {P} K D =
    let ops = OrderedPowerLawOps.ops O in
    record
      { Linf = KaplanBounds.Linf K
      ; Clo = PowerLawOps.mul ops (KaplanBounds.Blo K)
                (powNeg {ops = ops} D (betaExp P))
      ; Chi = PowerLawOps.mul ops (KaplanBounds.Bhi K)
                (powNeg {ops = ops} D (betaExp P))
      ; Alo = KaplanBounds.Alo K
      ; Ahi = KaplanBounds.Ahi K
      ; lower = λ N → KaplanBounds.lower K N D
      ; upper = λ N → KaplanBounds.upper K N D
      }

  kaplanBounds-sliceD
    : ∀ {O : OrderedPowerLawOps} {P : ResourcePrinciple}
    → AddSwap O
    → (K : KaplanBounds O P)
    → (N : PowerLawOps.R (OrderedPowerLawOps.ops O))
    → ExponentSliceBounds O (betaExp P)
        (λ D → KaplanBounds.loss K N D)
  kaplanBounds-sliceD {O} {P} swap K N =
    let open OrderedPowerLawOps O
        ops = OrderedPowerLawOps.ops O

        linf = KaplanBounds.Linf K
        clo =
          PowerLawOps.mul ops (KaplanBounds.Alo K)
            (powNeg {ops = ops} N (alphaExp P))
        chi =
          PowerLawOps.mul ops (KaplanBounds.Ahi K)
            (powNeg {ops = ops} N (alphaExp P))
    in
    record
      { Linf = linf
      ; Clo = clo
      ; Chi = chi
      ; Alo = KaplanBounds.Blo K
      ; Ahi = KaplanBounds.Bhi K
      ; lower = λ D →
          let var =
                PowerLawOps.mul ops (KaplanBounds.Blo K)
                  (powNeg {ops = ops} D (betaExp P))
              inner = AddSwap.add-swap swap var clo
              outer = add-mono (≤r-refl {x = linf}) inner
          in ≤r-trans outer (KaplanBounds.lower K N D)
      ; upper = λ D →
          let var =
                PowerLawOps.mul ops (KaplanBounds.Bhi K)
                  (powNeg {ops = ops} D (betaExp P))
              inner = AddSwap.add-swap swap chi var
              outer = add-mono (≤r-refl {x = linf}) inner
          in ≤r-trans (KaplanBounds.upper K N D) outer
      }

  deriveKaplanForm-witness
    : ∀ {ops : PowerLawOps}
    → (L : SeparablePowerLawLoss ops)
    → KaplanForm ops (SeparablePowerLawLoss.principle L)
  deriveKaplanForm-witness {ops} L =
    let open PowerLawOps ops in
    let P = SeparablePowerLawLoss.principle L
        loss = SeparablePowerLawLoss.loss L
        Linf = SeparablePowerLawLoss.Linf L
        f = SeparablePowerLawLoss.f L
        g = SeparablePowerLawLoss.g L
        sep = SeparablePowerLawLoss.sep L
        powF = SeparablePowerLawLoss.powF L
        powG = SeparablePowerLawLoss.powG L
        A = PowerLawWitness.A powF
        Af = PowerLawWitness.form powF
        B = PowerLawWitness.A powG
        Bg = PowerLawWitness.form powG
    in
    record
      { loss = loss
      ; Linf = Linf
      ; A = A
      ; B = B
      ; form = λ N D →
          trans
            (sep N D)
            (cong
              (PowerLawOps.add ops Linf)
              (cong₂
                (PowerLawOps.add ops)
                (Af N)
                (Bg D)))
      }

  module Experimental where
    -- Pre-scaling renormalization hooks (optional).
    record RenormPoint (ops : PowerLawOps) : Set (lsuc (lsuc ℓ)) where
      field
        N0 : PowerLawOps.R ops
        D0 : PowerLawOps.R ops
        L0 : PowerLawOps.R ops

    record PreScalingCalibration (ops : PowerLawOps) : Set (lsuc (lsuc ℓ)) where
      field
        loss : PowerLawOps.R ops → PowerLawOps.R ops → PowerLawOps.R ops
        ref : RenormPoint ops

    record RenormalizedKaplan (ops : PowerLawOps) (P : ResourcePrinciple)
      : Set (lsuc (lsuc ℓ)) where
      field
        base : KaplanForm ops P
        ref : RenormPoint ops
        renorm
          : KaplanForm.loss base
              (RenormPoint.N0 ref)
              (RenormPoint.D0 ref)
            ≡ RenormPoint.L0 ref

    record PredictiveKaplan (ops : PowerLawOps) (P : ResourcePrinciple)
      : Set (lsuc (lsuc ℓ)) where
      field
        calib : PreScalingCalibration ops
        scaling : KaplanForm ops P
        lossMatch
          : ∀ N D
          → KaplanForm.loss scaling N D
            ≡ PreScalingCalibration.loss calib N D
        renorm
          : PreScalingCalibration.loss calib
              (RenormPoint.N0 (PreScalingCalibration.ref calib))
              (RenormPoint.D0 (PreScalingCalibration.ref calib))
            ≡ RenormPoint.L0 (PreScalingCalibration.ref calib)

    predictiveKaplan-renorm
      : ∀ {ops : PowerLawOps} {P : ResourcePrinciple}
      → PredictiveKaplan ops P
      → RenormalizedKaplan ops P
    predictiveKaplan-renorm {ops} {P} K =
      let calib = PredictiveKaplan.calib K
          scaling = PredictiveKaplan.scaling K
          ref = PreScalingCalibration.ref calib
          lossMatch = PredictiveKaplan.lossMatch K
          renorm0 = PredictiveKaplan.renorm K
      in record
        { base = scaling
        ; ref = ref
        ; renorm =
            trans
              (lossMatch (RenormPoint.N0 ref) (RenormPoint.D0 ref))
              renorm0
        }

    predictiveKaplan-predict
      : ∀ {ops : PowerLawOps} {P : ResourcePrinciple}
      → (K : PredictiveKaplan ops P)
      → KaplanForm.loss (PredictiveKaplan.scaling K)
          (RenormPoint.N0 (PreScalingCalibration.ref (PredictiveKaplan.calib K)))
          (RenormPoint.D0 (PreScalingCalibration.ref (PredictiveKaplan.calib K)))
        ≡ RenormPoint.L0 (PreScalingCalibration.ref (PredictiveKaplan.calib K))
    predictiveKaplan-predict {ops} {P} K =
      let calib = PredictiveKaplan.calib K
          ref = PreScalingCalibration.ref calib
          lossMatch = PredictiveKaplan.lossMatch K
          renorm0 = PredictiveKaplan.renorm K
      in trans
           (lossMatch (RenormPoint.N0 ref) (RenormPoint.D0 ref))
           renorm0

  record ExcessLossHomogeneous (ops : PowerLawOps) (P : ResourcePrinciple)
    : Set (lsuc (lsuc ℓ)) where
    field
      lossC : PowerLawOps.R ops → PowerLawOps.R ops
      homC : Homogeneous ops (ResourcePrinciple.lossExponent P) lossC

  record ExcessLossPowerLaw (ops : PowerLawOps) (P : ResourcePrinciple)
    : Set (lsuc (lsuc ℓ)) where
    field
      lossC : PowerLawOps.R ops → PowerLawOps.R ops
      powC : PowerLawWitness ops (ResourcePrinciple.lossExponent P) lossC

  record ExcessLossPowerLawBand (O : OrderedPowerLawOps) (P : ResourcePrinciple)
    : Set (lsuc (lsuc ℓ)) where
    field
      lossC : PowerLawOps.R (OrderedPowerLawOps.ops O)
              → PowerLawOps.R (OrderedPowerLawOps.ops O)
      bandC : PowerLawBand O (ResourcePrinciple.lossExponent P) lossC

  record ComputePowerLaw (ops : PowerLawOps) (P : ResourcePrinciple)
    : Set (lsuc (lsuc ℓ)) where
    field
      lossC : PowerLawOps.R ops → PowerLawOps.R ops
      Kc : PowerLawOps.R ops
      form : ∀ C → lossC C
        ≡ PowerLawOps.mul ops Kc (powNeg {ops} C (ResourcePrinciple.lossExponent P))

  deriveComputePowerLaw
    : ∀ {ops : PowerLawOps} {P : ResourcePrinciple}
    → PowerLawAxiom ops
    → ExcessLossHomogeneous ops P
    → ComputePowerLaw ops P
  deriveComputePowerLaw {ops} {P} ax L =
    let open PowerLawOps ops in
    let lossC = ExcessLossHomogeneous.lossC L
        homC = ExcessLossHomogeneous.homC L
        Kc = proj₁ (PowerLawAxiom.characterize ax homC)
        Kform = proj₂ (PowerLawAxiom.characterize ax homC)
    in
    record
      { lossC = lossC
      ; Kc = Kc
      ; form = Kform
      }

  deriveComputePowerLaw-witness
    : ∀ {ops : PowerLawOps} {P : ResourcePrinciple}
    → ExcessLossPowerLaw ops P
    → ComputePowerLaw ops P
  deriveComputePowerLaw-witness {ops} {P} L =
    let lossC = ExcessLossPowerLaw.lossC L
        powC = ExcessLossPowerLaw.powC L
        Kc = PowerLawWitness.A powC
        Kform = PowerLawWitness.form powC
    in
    record
      { lossC = lossC
      ; Kc = Kc
      ; form = Kform
      }

  record ComputeBounds (O : OrderedPowerLawOps) (P : ResourcePrinciple)
    : Set (lsuc (lsuc ℓ)) where
    field
      lossC : PowerLawOps.R (OrderedPowerLawOps.ops O)
              → PowerLawOps.R (OrderedPowerLawOps.ops O)
      Alo : PowerLawOps.R (OrderedPowerLawOps.ops O)
      Ahi : PowerLawOps.R (OrderedPowerLawOps.ops O)
      lower
        : ∀ C
        → OrderedPowerLawOps._≤r_ O
            (PowerLawOps.mul (OrderedPowerLawOps.ops O) Alo
              (powNeg {ops = OrderedPowerLawOps.ops O}
                C (ResourcePrinciple.lossExponent P)))
            (lossC C)
      upper
        : ∀ C
        → OrderedPowerLawOps._≤r_ O
            (lossC C)
            (PowerLawOps.mul (OrderedPowerLawOps.ops O) Ahi
              (powNeg {ops = OrderedPowerLawOps.ops O}
                C (ResourcePrinciple.lossExponent P)))

  deriveComputeBounds
    : ∀ {O : OrderedPowerLawOps} {P : ResourcePrinciple}
    → ExcessLossPowerLawBand O P
    → ComputeBounds O P
  deriveComputeBounds {O} {P} L =
    let lossC = ExcessLossPowerLawBand.lossC L
        bandC = ExcessLossPowerLawBand.bandC L
        Alo = PowerLawBand.Alo bandC
        Ahi = PowerLawBand.Ahi bandC
        lower = PowerLawBand.lower bandC
        upper = PowerLawBand.upper bandC
    in
    record
      { lossC = lossC
      ; Alo = Alo
      ; Ahi = Ahi
      ; lower = lower
      ; upper = upper
      }

  computeBounds-band
    : ∀ {O : OrderedPowerLawOps} {P : ResourcePrinciple}
    → (B : ComputeBounds O P)
    → PowerLawBand O (ResourcePrinciple.lossExponent P)
        (ComputeBounds.lossC B)
  computeBounds-band B =
    record
      { Alo = ComputeBounds.Alo B
      ; Ahi = ComputeBounds.Ahi B
      ; lower = ComputeBounds.lower B
      ; upper = ComputeBounds.upper B
      }

  record PipelineAssumptionBoundary {g : Scale} (ops : PowerLawOps)
    : Set (lsuc (lsuc ℓ)) where
    field
      assumptions : PipelineAssumptions {g}
      powerLawAxiom : PowerLawAxiom ops
      separableLoss : SeparableHomogeneousLoss ops
      excessLoss
        : ExcessLossHomogeneous ops
            (SeparableHomogeneousLoss.principle separableLoss)

    principle : ResourcePrinciple
    principle = SeparableHomogeneousLoss.principle separableLoss

    pipelineModel : Pipeline {g}
    pipelineModel = pipelineFromAssumptions assumptions

    kaplan : KaplanForm ops principle
    kaplan = deriveKaplanForm powerLawAxiom separableLoss

    computeLaw : ComputePowerLaw ops principle
    computeLaw = deriveComputePowerLaw powerLawAxiom excessLoss

  boundary-scaling-summary
    : ∀ {g} {ops : PowerLawOps}
    → (B : PipelineAssumptionBoundary {g} ops)
    → (dimCompute dimData
        : RG.ScalingDimension
            (Pipeline.step (PipelineAssumptionBoundary.pipelineModel B)))
    → Pipeline.ScalingRegimesSummary
        (PipelineAssumptionBoundary.pipelineModel B) dimCompute dimData
  boundary-scaling-summary B dimCompute dimData =
    Pipeline.scalingRegimes-summary
      (PipelineAssumptionBoundary.pipelineModel B) dimCompute dimData

  record PipelineAssumptionBoundaryWeak {g : Scale} (ops : PowerLawOps)
    : Set (lsuc (lsuc ℓ)) where
    field
      assumptions : PipelineAssumptions {g}
      separableLoss : SeparablePowerLawLoss ops
      excessLoss
        : ExcessLossPowerLaw ops
            (SeparablePowerLawLoss.principle separableLoss)

    principle : ResourcePrinciple
    principle = SeparablePowerLawLoss.principle separableLoss

    pipelineModel : Pipeline {g}
    pipelineModel = pipelineFromAssumptions assumptions

    kaplan : KaplanForm ops principle
    kaplan = deriveKaplanForm-witness separableLoss

    computeLaw : ComputePowerLaw ops principle
    computeLaw = deriveComputePowerLaw-witness excessLoss

  boundary-scaling-summary-weak
    : ∀ {g} {ops : PowerLawOps}
    → (B : PipelineAssumptionBoundaryWeak {g} ops)
    → (dimCompute dimData
        : RG.ScalingDimension
            (Pipeline.step (PipelineAssumptionBoundaryWeak.pipelineModel B)))
    → Pipeline.ScalingRegimesSummary
        (PipelineAssumptionBoundaryWeak.pipelineModel B) dimCompute dimData
  boundary-scaling-summary-weak B dimCompute dimData =
    Pipeline.scalingRegimes-summary
      (PipelineAssumptionBoundaryWeak.pipelineModel B) dimCompute dimData

  record PipelineAssumptionBoundaryBand {g : Scale} (O : OrderedPowerLawOps)
    : Set (lsuc (lsuc ℓ)) where
    field
      assumptions : PipelineAssumptions {g}
      addSwap : AddSwap O
      separableLoss : SeparablePowerLawBandLoss O
      excessLoss
        : ExcessLossPowerLawBand O
            (SeparablePowerLawBandLoss.principle separableLoss)

    principle : ResourcePrinciple
    principle = SeparablePowerLawBandLoss.principle separableLoss

    pipelineModel : Pipeline {g}
    pipelineModel = pipelineFromAssumptions assumptions

    kaplanBounds : KaplanBounds O principle
    kaplanBounds = deriveKaplanBounds separableLoss

    computeBounds : ComputeBounds O principle
    computeBounds = deriveComputeBounds excessLoss

  boundary-scaling-summary-band
    : ∀ {g} {O : OrderedPowerLawOps}
    → (B : PipelineAssumptionBoundaryBand {g} O)
    → (dimCompute dimData
        : RG.ScalingDimension
            (Pipeline.step (PipelineAssumptionBoundaryBand.pipelineModel B)))
    → Pipeline.ScalingRegimesSummary
        (PipelineAssumptionBoundaryBand.pipelineModel B) dimCompute dimData
  boundary-scaling-summary-band B dimCompute dimData =
    Pipeline.scalingRegimes-summary
      (PipelineAssumptionBoundaryBand.pipelineModel B) dimCompute dimData

  record ScalingBandSummary
    {g : Scale} {O : OrderedPowerLawOps}
    (B : PipelineAssumptionBoundaryBand {g} O)
    (dimCompute dimData
      : RG.ScalingDimension
          (Pipeline.step (PipelineAssumptionBoundaryBand.pipelineModel B)))
    : Set (lsuc (lsuc ℓ)) where
    field
      summary
        : Pipeline.ScalingRegimesSummary
            (PipelineAssumptionBoundaryBand.pipelineModel B)
            dimCompute dimData
      kaplan : KaplanBounds O (PipelineAssumptionBoundaryBand.principle B)
      compute : ComputeBounds O (PipelineAssumptionBoundaryBand.principle B)
      sliceN
        : ∀ D
        → ExponentSliceBounds O
            (alphaExp (PipelineAssumptionBoundaryBand.principle B))
            (λ N → KaplanBounds.loss kaplan N D)
      sliceD
        : ∀ N
        → ExponentSliceBounds O
            (betaExp (PipelineAssumptionBoundaryBand.principle B))
            (λ D → KaplanBounds.loss kaplan N D)
      computeSlice
        : PowerLawBand O
            (ResourcePrinciple.lossExponent
              (PipelineAssumptionBoundaryBand.principle B))
            (ComputeBounds.lossC compute)

  scaling-band-summary
    : ∀ {g} {O : OrderedPowerLawOps}
    → (B : PipelineAssumptionBoundaryBand {g} O)
    → (dimCompute dimData
        : RG.ScalingDimension
            (Pipeline.step (PipelineAssumptionBoundaryBand.pipelineModel B)))
    → ScalingBandSummary B dimCompute dimData
  scaling-band-summary B dimCompute dimData =
    let kaplan = PipelineAssumptionBoundaryBand.kaplanBounds B
        compute = PipelineAssumptionBoundaryBand.computeBounds B
    in
    record
      { summary = boundary-scaling-summary-band B dimCompute dimData
      ; kaplan = kaplan
      ; compute = compute
      ; sliceN = λ D → kaplanBounds-sliceN kaplan D
      ; sliceD = λ N → kaplanBounds-sliceD (PipelineAssumptionBoundaryBand.addSwap B) kaplan N
      ; computeSlice = computeBounds-band compute
      }

  record ToyTransformerBandBoundary {g : Scale} (O : OrderedPowerLawOps)
    : Set (lsuc (lsuc ℓ)) where
    field
      assumptions : PipelineAssumptions {g}
      addSwap : AddSwap O
      bandLoss : SeparablePowerLawBandLoss O
      excessLoss
        : ExcessLossPowerLawBand O
            (SeparablePowerLawBandLoss.principle bandLoss)
      principle-toy
        : SeparablePowerLawBandLoss.principle bandLoss ≡ toyUnitPrinciple

    boundary : PipelineAssumptionBoundaryBand {g} O
    boundary =
      record
        { assumptions = assumptions
        ; addSwap = addSwap
        ; separableLoss = bandLoss
        ; excessLoss = excessLoss
        }

    computeExponent
      : ResourcePrinciple.computeExponent
          (PipelineAssumptionBoundaryBand.principle boundary)
        ≡ ratio 1 2 (nonZeroSuc 1)
    computeExponent =
      subst
        (λ P → ResourcePrinciple.computeExponent P ≡ ratio 1 2 (nonZeroSuc 1))
        (sym principle-toy)
        toyUnitComputeExponent

    dataExponent
      : ResourcePrinciple.dataExponent
          (PipelineAssumptionBoundaryBand.principle boundary)
        ≡ ratio 1 2 (nonZeroSuc 1)
    dataExponent =
      subst
        (λ P → ResourcePrinciple.dataExponent P ≡ ratio 1 2 (nonZeroSuc 1))
        (sym principle-toy)
        toyUnitDataExponent

    lossExponent
      : ResourcePrinciple.lossExponent
          (PipelineAssumptionBoundaryBand.principle boundary)
        ≡ ratio 1 2 (nonZeroSuc 1)
    lossExponent =
      subst
        (λ P → ResourcePrinciple.lossExponent P ≡ ratio 1 2 (nonZeroSuc 1))
        (sym principle-toy)
        toyUnitLossExponent

  module ExperimentalCompute where
    -- Pre-scaling renormalization hooks for compute-only laws (optional).
    record RenormComputePoint (ops : PowerLawOps) : Set (lsuc (lsuc ℓ)) where
      field
        C0 : PowerLawOps.R ops
        L0 : PowerLawOps.R ops

    record PreScalingComputeCalibration (ops : PowerLawOps) : Set (lsuc (lsuc ℓ)) where
      field
        lossC : PowerLawOps.R ops → PowerLawOps.R ops
        ref : RenormComputePoint ops

    record RenormalizedComputePowerLaw (ops : PowerLawOps) (P : ResourcePrinciple)
      : Set (lsuc (lsuc ℓ)) where
      field
        base : ComputePowerLaw ops P
        ref : RenormComputePoint ops
        renorm
          : ComputePowerLaw.lossC base (RenormComputePoint.C0 ref)
            ≡ RenormComputePoint.L0 ref

    record PredictiveComputePowerLaw (ops : PowerLawOps) (P : ResourcePrinciple)
      : Set (lsuc (lsuc ℓ)) where
      field
        calib : PreScalingComputeCalibration ops
        scaling : ComputePowerLaw ops P
        lossMatch
          : ∀ C
          → ComputePowerLaw.lossC scaling C
            ≡ PreScalingComputeCalibration.lossC calib C
        renorm
          : PreScalingComputeCalibration.lossC calib
              (RenormComputePoint.C0 (PreScalingComputeCalibration.ref calib))
            ≡ RenormComputePoint.L0 (PreScalingComputeCalibration.ref calib)

    predictiveCompute-renorm
      : ∀ {ops : PowerLawOps} {P : ResourcePrinciple}
      → PredictiveComputePowerLaw ops P
      → RenormalizedComputePowerLaw ops P
    predictiveCompute-renorm {ops} {P} K =
      let calib = PredictiveComputePowerLaw.calib K
          scaling = PredictiveComputePowerLaw.scaling K
          ref = PreScalingComputeCalibration.ref calib
          lossMatch = PredictiveComputePowerLaw.lossMatch K
          renorm0 = PredictiveComputePowerLaw.renorm K
      in record
        { base = scaling
        ; ref = ref
        ; renorm =
            trans
              (lossMatch (RenormComputePoint.C0 ref))
              renorm0
        }

    predictiveCompute-predict
      : ∀ {ops : PowerLawOps} {P : ResourcePrinciple}
      → (K : PredictiveComputePowerLaw ops P)
      → ComputePowerLaw.lossC (PredictiveComputePowerLaw.scaling K)
          (RenormComputePoint.C0
            (PreScalingComputeCalibration.ref
              (PredictiveComputePowerLaw.calib K)))
        ≡ RenormComputePoint.L0
            (PreScalingComputeCalibration.ref
              (PredictiveComputePowerLaw.calib K))
    predictiveCompute-predict {ops} {P} K =
      let calib = PredictiveComputePowerLaw.calib K
          ref = PreScalingComputeCalibration.ref calib
          lossMatch = PredictiveComputePowerLaw.lossMatch K
          renorm0 = PredictiveComputePowerLaw.renorm K
      in trans
           (lossMatch (RenormComputePoint.C0 ref))
           renorm0

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

  module Examples where
    record SGDExample {g : Scale} : Set (lsuc (lsuc ℓ)) where
      field
        assumptions : PipelineAssumptions {g}
        pipeline : Pipeline {g}
        sgd : TB.SGDTraining g
        nextTokenLoss
          : TB.NextTokenLossObservableFromData
              (TB.TrainingSpec.bridge
                (PipelineAssumptions.spec assumptions))

    record AdamExample {g : Scale} : Set (lsuc (lsuc ℓ)) where
      field
        assumptions : PipelineAssumptions {g}
        pipeline : Pipeline {g}
        adam : TB.AdamTraining g
        nextTokenLoss
          : TB.NextTokenLossObservableFromData
              (TB.TrainingSpec.bridge
                (PipelineAssumptions.spec assumptions))
