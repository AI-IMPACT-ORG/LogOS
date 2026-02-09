{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Arguments.TransformerScalingPipeline.ExperimentalCompute where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel.Graded using (GradedKernel)

import LogOS.Packs.Agents.Experimental.Arguments.TransformerScalingPipeline.ResourcePrinciple as ResourcePrinciple
import LogOS.Packs.Agents.Experimental.Arguments.TransformerScalingPipeline.PowerLaw as PowerLaw
import LogOS.Packs.Agents.Experimental.Arguments.TransformerScalingPipeline.Calibration as Calibration

-- Optional hooks for compute-only scaling calibration.

module For
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO)
            (BulkBoundary.bnd (GradedKernel.BB K)))
  where

  module RP = ResourcePrinciple.For K ωCPO
  open RP

  module PL = PowerLaw.For K ωCPO
  open PL

  module Cal = Calibration.For K ωCPO
  open Cal

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

