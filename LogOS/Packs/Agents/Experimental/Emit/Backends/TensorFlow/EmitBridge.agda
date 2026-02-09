{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.EmitBridge where

open import LogOS.Packs.Agents.Emit.IR.Backend using (Backend)

module For (B : Backend) where

  open import LogOS.Prelude
  open import LogOS.Prelude.List using ([])
  open import LogOS.Base.Signature using (LogOSSignature)
  open import LogOS.Minimal.Adapter using (QAdapter)
  open import LogOS.Minimal.Con using (BulkBoundary)
  open import LogOS.Minimal.Truth as Truth
  open import LogOS.Kernel.Graded using (GradedKernel)

  import LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.EmitCore as EmitCore
  import LogOS.Packs.Agents.Experimental.Arguments.TransformerBridge as TransformerBridge
  import LogOS.Packs.Agents.Emit.IR.Intent as Intent
  open import LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.Types

  module Core = EmitCore.For B

  module WithBridge
    {ℓ : Level}
    {Sig : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO)
              (BulkBoundary.bnd (GradedKernel.BB K)))
    where

    module TB = TransformerBridge.For K ωCPO
    open QAdapter Q using (Scale)

    optimizerFromTag : TB.Training.OptimizerTag → TFOptimizer
    optimizerFromTag TB.Training.sgd = Intent.sgd
    optimizerFromTag TB.Training.adam = Intent.adam

    optimizerFromTagged : ∀ {g} → TB.Training.TaggedTraining g → TFOptimizer
    optimizerFromTagged T = optimizerFromTag (TB.Training.TaggedTraining.tag T)

    optimizerFromSGD : ∀ {g} → TB.Training.SGDTraining g → TFOptimizer
    optimizerFromSGD _ = optimizerFromTag TB.Training.sgd

    optimizerFromAdam : ∀ {g} → TB.Training.AdamTraining g → TFOptimizer
    optimizerFromAdam _ = optimizerFromTag TB.Training.adam

    lossFromNextToken : ∀ {B} → TB.Training.NextTokenLossObservableFromData B → TFLoss
    lossFromNextToken _ = Intent.sparseCategorical

    record TFTrainingHooks (g : Scale) : Set (lsuc (lsuc ℓ)) where
      field
        spec : TB.Training.TrainingSpec g
        optimizer : TFOptimizer
        loss : TFLoss

    defaultTrainingParamsFromHooks
      : ∀ {g} → TFTrainingHooks g → TFTrainingParams
    defaultTrainingParamsFromHooks hooks =
      record
        { datasetVar = "dataset"
        ; inputVar = "x"
        ; targetVar = "y"
        ; taskVar = "task_id"
        ; learningRate = Intent.param "learning_rate"
        ; epochs = Intent.param "epochs"
        ; optimizer = TFTrainingHooks.optimizer hooks
        ; loss = TFTrainingHooks.loss hooks
        ; schedule = Intent.constant
        ; dataShape = Intent.paired
        ; dataOps = []
        ; telemetry = Intent.defaultTelemetry
        }

    emitSpecFromHooks : ∀ {g} → TFHyperParams → TFTrainingHooks g → TFEmitSpec
    emitSpecFromHooks h hooks =
      record
        { family = Intent.decoderOnly
        ; hyper = h
        ; train = defaultTrainingParamsFromHooks hooks
        ; symbolic = Intent.defaultSymbolic
        ; coupling = Intent.defaultCoupling
        }
