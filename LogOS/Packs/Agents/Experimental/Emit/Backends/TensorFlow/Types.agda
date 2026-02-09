{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.Types where

open import LogOS.Prelude.List using (List; []; _∷_)
open import LogOS.Prelude using (ℕ)
open import LogOS.Prelude.String using (String)

import LogOS.Packs.Agents.Emit.IR.Intent as Intent
open Intent using (param; literal; litNat)

TFArg : Set
TFArg = Intent.EmitArg

TFOptimizer : Set
TFOptimizer = Intent.OptimizerIntent

renderOptimizer : TFOptimizer → String
renderOptimizer Intent.adam = "Adam"
renderOptimizer Intent.sgd = "SGD"
renderOptimizer (Intent.customOptimizer s) = s

TFLoss : Set
TFLoss = Intent.LossIntent

renderLoss : TFLoss → String
renderLoss Intent.sparseCategorical =
  "tf.keras.losses.SparseCategoricalCrossentropy(from_logits=True, reduction=\"none\")"
renderLoss (Intent.customLoss s) = s

record TFHyperParams : Set where
  field
    srcVocab : TFArg
    tgtVocab : TFArg
    modelDim : TFArg
    headCount : TFArg
    layerCount : TFArg
    ffnDim : TFArg
    maxLen : TFArg
    dropout : TFArg
    constraints : List Intent.ModelConstraint

record TFTrainingParams : Set where
  field
    datasetVar : String
    inputVar : String
    targetVar : String
    taskVar : String
    learningRate : TFArg
    epochs : TFArg
    optimizer : TFOptimizer
    loss : TFLoss
    schedule : Intent.ScheduleIntent
    dataShape : Intent.DataShape
    dataOps : List Intent.DataOp
    telemetry : Intent.TelemetryIntent

record TFEmitSpec : Set where
  field
    family : Intent.ModelFamily
    hyper : TFHyperParams
    train : TFTrainingParams
    symbolic : Intent.SymbolicIntent
    coupling : Intent.CouplingIntent

defaultHyper : TFHyperParams
defaultHyper =
  record
    { srcVocab = param "vocab_size"
    ; tgtVocab = param "vocab_size"
    ; modelDim = param "d_model"
    ; headCount = param "n_heads"
    ; layerCount = param "n_layers"
    ; ffnDim = param "d_ff"
    ; maxLen = param "max_len"
    ; dropout = param "dropout"
    ; constraints = Intent.causalMask ∷ []
    }

defaultTraining : TFTrainingParams
defaultTraining =
  record
    { datasetVar = "dataset"
    ; inputVar = "x"
    ; targetVar = "y"
    ; taskVar = "task_id"
    ; learningRate = param "learning_rate"
    ; epochs = param "epochs"
    ; optimizer = Intent.adam
    ; loss = Intent.sparseCategorical
    ; schedule = Intent.constant
    ; dataShape = Intent.paired
    ; dataOps = []
    ; telemetry = Intent.defaultTelemetry
    }

defaultSpec : TFEmitSpec
defaultSpec =
  record
    { family = Intent.decoderOnly
    ; hyper = defaultHyper
    ; train = defaultTraining
    ; symbolic = Intent.defaultSymbolic
    ; coupling = Intent.defaultCoupling
    }

literalHyper
  : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → String → TFHyperParams
literalHyper srcVocab tgtVocab dim heads layers ffn maxLen dropout =
  record
    { srcVocab = litNat srcVocab
    ; tgtVocab = litNat tgtVocab
    ; modelDim = litNat dim
    ; headCount = litNat heads
    ; layerCount = litNat layers
    ; ffnDim = litNat ffn
    ; maxLen = litNat maxLen
    ; dropout = literal dropout
    ; constraints = Intent.causalMask ∷ []
    }

hyperFromIntent : Intent.ModelIntent → TFHyperParams
hyperFromIntent m =
  record
    { srcVocab = Intent.ModelIntent.srcVocab m
    ; tgtVocab = Intent.ModelIntent.tgtVocab m
    ; modelDim = Intent.ModelIntent.modelDim m
    ; headCount = Intent.ModelIntent.headCount m
    ; layerCount = Intent.ModelIntent.layerCount m
    ; ffnDim = Intent.ModelIntent.ffnDim m
    ; maxLen = Intent.ModelIntent.maxLen m
    ; dropout = Intent.ModelIntent.dropout m
    ; constraints = Intent.ModelIntent.constraints m
    }

trainingFromIntent
  : Intent.TrainingIntent → Intent.DataIntent → Intent.TelemetryIntent → TFTrainingParams
trainingFromIntent tr dat tel =
  record
    { datasetVar = Intent.DataIntent.datasetVar dat
    ; inputVar = Intent.DataIntent.inputVar dat
    ; targetVar = Intent.DataIntent.targetVar dat
    ; taskVar = Intent.DataIntent.taskVar dat
    ; learningRate = Intent.TrainingIntent.learningRate tr
    ; epochs = Intent.TrainingIntent.epochs tr
    ; optimizer = Intent.TrainingIntent.optimizer tr
    ; loss = Intent.TrainingIntent.loss tr
    ; schedule = Intent.TrainingIntent.schedule tr
    ; dataShape = Intent.DataIntent.shape dat
    ; dataOps = Intent.DataIntent.pipeline dat
    ; telemetry = tel
    }

emitSpecFromIntent : Intent.EmitIntent → TFEmitSpec
emitSpecFromIntent intent =
  record
    { family = Intent.ModelIntent.family (Intent.EmitIntent.model intent)
    ; hyper = hyperFromIntent (Intent.EmitIntent.model intent)
    ; train =
        trainingFromIntent
          (Intent.EmitIntent.training intent)
          (Intent.EmitIntent.dataIntent intent)
          (Intent.EmitIntent.telemetry intent)
    ; symbolic = Intent.EmitIntent.symbolic intent
    ; coupling = Intent.EmitIntent.coupling intent
    }
