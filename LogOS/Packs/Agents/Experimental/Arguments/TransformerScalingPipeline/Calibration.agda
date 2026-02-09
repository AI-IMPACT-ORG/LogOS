{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Arguments.TransformerScalingPipeline.Calibration where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel.Graded using (GradedKernel)

import LogOS.Packs.Agents.Experimental.Arguments.TransformerScalingPipeline.Core as CoreMod
import LogOS.Packs.Agents.Experimental.Arguments.TransformerScalingPipeline.ResourcePrinciple as ResourcePrinciple
import LogOS.Packs.Agents.Experimental.Arguments.TransformerScalingPipeline.PowerLaw as PowerLaw

-- Tie pipeline assumptions to resource-principle / power-law surfaces.

module For
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO)
            (BulkBoundary.bnd (GradedKernel.BB K)))
  where

  module Core = CoreMod.For K ωCPO
  open Core

  module RP = ResourcePrinciple.For K ωCPO
  open RP

  module PL = PowerLaw.For K ωCPO
  open PL

  open QAdapter Q using (Scale)

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
        Kchar = PowerLawAxiom.characterize ax homC
        Kc = proj₁ Kchar
        Kform = proj₂ Kchar
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
    : Set (lsuc (lsuc (lsuc ℓ))) where
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
    : Set (lsuc (lsuc (lsuc ℓ))) where
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
    : Set (lsuc (lsuc (lsuc ℓ))) where
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
    : Set (lsuc (lsuc (lsuc ℓ))) where
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

  record UnitTransformerBandBoundary {g : Scale} (O : OrderedPowerLawOps)
    : Set (lsuc (lsuc (lsuc ℓ))) where
    field
      assumptions : PipelineAssumptions {g}
      addSwap : AddSwap O
      bandLoss : SeparablePowerLawBandLoss O
      excessLoss
        : ExcessLossPowerLawBand O
            (SeparablePowerLawBandLoss.principle bandLoss)
      principle-unit
        : SeparablePowerLawBandLoss.principle bandLoss ≡ unitPrinciple

    boundary : PipelineAssumptionBoundaryBand {g} O
    boundary =
      record
        { assumptions = assumptions
        ; addSwap = addSwap
        ; separableLoss = bandLoss
        ; excessLoss = excessLoss
        }

    principle
      : ResourcePrinciple
    principle = PipelineAssumptionBoundaryBand.principle boundary

    computeExponent
      : ResourcePrinciple.computeExponent
          principle
        ≡ ratio 1 2 (nonZeroSuc 1)
    computeExponent =
      subst
        (λ P → ResourcePrinciple.computeExponent P ≡ ratio 1 2 (nonZeroSuc 1))
        (sym principle-unit)
        unitComputeExponent

    dataExponent
      : ResourcePrinciple.dataExponent
          principle
        ≡ ratio 1 2 (nonZeroSuc 1)
    dataExponent =
      subst
        (λ P → ResourcePrinciple.dataExponent P ≡ ratio 1 2 (nonZeroSuc 1))
        (sym principle-unit)
        unitDataExponent

    lossExponent
      : ResourcePrinciple.lossExponent
          principle
        ≡ ratio 1 2 (nonZeroSuc 1)
    lossExponent =
      subst
        (λ P → ResourcePrinciple.lossExponent P ≡ ratio 1 2 (nonZeroSuc 1))
        (sym principle-unit)
        unitLossExponent
