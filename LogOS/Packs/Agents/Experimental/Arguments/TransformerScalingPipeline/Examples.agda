{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Arguments.TransformerScalingPipeline.Examples where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel.Graded using (GradedKernel)

import LogOS.Packs.Agents.Experimental.Arguments.TransformerScalingPipeline.Core as CoreMod

-- Small record shells to make examples constructible without committing to a backend.

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

  open QAdapter Q using (Scale)

  module Examples where
    record SGDExample {g : Scale} : Set (lsuc (lsuc (lsuc ℓ))) where
      field
        assumptions : PipelineAssumptions {g}
        pipeline : Pipeline {g}
        sgd : TB.Training.SGDTraining g
        nextTokenLoss
          : TB.Training.NextTokenLossObservableFromData
              (TB.Training.TrainingSpec.bridge
                (PipelineAssumptions.spec assumptions))

    record AdamExample {g : Scale} : Set (lsuc (lsuc (lsuc ℓ))) where
      field
        assumptions : PipelineAssumptions {g}
        pipeline : Pipeline {g}
        adam : TB.Training.AdamTraining g
        nextTokenLoss
          : TB.Training.NextTokenLossObservableFromData
              (TB.Training.TrainingSpec.bridge
                (PipelineAssumptions.spec assumptions))
