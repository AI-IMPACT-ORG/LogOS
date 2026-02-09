{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Emit.IR.Intent where

open import LogOS.Prelude.List using (List; []; _∷_)
open import LogOS.Prelude using (ℕ)
open import LogOS.Prelude.String using (String; _++s_; intercalateS)
open import LogOS.Prelude.NatShow using (showNat)
open import LogOS.Prelude.Bool using (Bool; true; false)

data EmitArg : Set where
  param : String → EmitArg
  literal : String → EmitArg

renderArg : EmitArg → String
renderArg (param s) = s
renderArg (literal s) = s

litNat : ℕ → EmitArg
litNat n = literal (showNat n)

paramNames : List EmitArg → List String
paramNames [] = []
paramNames (param name ∷ xs) = name ∷ paramNames xs
paramNames (literal _ ∷ xs) = paramNames xs

argList : List EmitArg → String
argList args = intercalateS ", " (paramNames args)

data ModelFamily : Set where
  decoderOnly : ModelFamily
  encoderDecoder : ModelFamily
  mlpBaseline : ModelFamily

data ModelConstraint : Set where
  causalMask : ModelConstraint
  noDropout : ModelConstraint

data SymbolicConstraint : Set where
  invariant : String → SymbolicConstraint
  rewriteRule : String → SymbolicConstraint
  safetyBarrier : String → SymbolicConstraint
  typeConstraint : String → SymbolicConstraint
  budgetConstraint : String → SymbolicConstraint

record SymbolicIntent : Set where
  field
    constraints : List SymbolicConstraint
    proofObligations : List String
    notes : List String

record ModelIntent : Set where
  field
    family : ModelFamily
    srcVocab : EmitArg
    tgtVocab : EmitArg
    modelDim : EmitArg
    headCount : EmitArg
    layerCount : EmitArg
    ffnDim : EmitArg
    maxLen : EmitArg
    dropout : EmitArg
    constraints : List ModelConstraint

data ScheduleIntent : Set where
  constant : ScheduleIntent
  linearDecay : EmitArg → EmitArg → ScheduleIntent

data OptimizerIntent : Set where
  adam : OptimizerIntent
  sgd : OptimizerIntent
  customOptimizer : String → OptimizerIntent

data LossIntent : Set where
  sparseCategorical : LossIntent
  customLoss : String → LossIntent

data DataShape : Set where
  tokensOnly : DataShape
  paired : DataShape
  taskTokens : DataShape
  taskPaired : DataShape

data DataOp : Set where
  shiftRight : DataOp

record DataIntent : Set where
  field
    datasetVar : String
    inputVar : String
    targetVar : String
    taskVar : String
    shape : DataShape
    pipeline : List DataOp

data CouplingStrategy : Set where
  guidedDecode : CouplingStrategy
  lossPenalty : CouplingStrategy
  constraintProjection : CouplingStrategy
  rejectionSampling : CouplingStrategy
  ruleAugmentedData : CouplingStrategy
  posteriorRegularization : CouplingStrategy
  proofGuidedSearch : CouplingStrategy

record CouplingIntent : Set where
  field
    strategies : List CouplingStrategy
    strength : EmitArg
    schedule : ScheduleIntent
    notes : List String

data TelemetrySignal : Set where
  lossCurve : TelemetrySignal
  gradNorm : TelemetrySignal
  stepTime : TelemetrySignal
  tokensPerSecond : TelemetrySignal
  taskId : TelemetrySignal
  taskLoss : TelemetrySignal
  forgettingProxy : TelemetrySignal
  driftScore : TelemetrySignal
  stabilityScore : TelemetrySignal
  bufferSize : TelemetrySignal

record ContinualTelemetry : Set where
  field
    enabled : Bool
    emaAlpha : EmitArg
    taskVar : String
    bufferVar : String

record TelemetryIntent : Set where
  field
    signals : List TelemetrySignal
    everySteps : EmitArg
    continual : ContinualTelemetry

record TrainingIntent : Set where
  field
    epochs : EmitArg
    learningRate : EmitArg
    schedule : ScheduleIntent
    optimizer : OptimizerIntent
    loss : LossIntent

record EmitIntent : Set where
  field
    model : ModelIntent
    dataIntent : DataIntent
    training : TrainingIntent
    telemetry : TelemetryIntent
    symbolic : SymbolicIntent
    coupling : CouplingIntent

defaultModel : ModelIntent
defaultModel =
  record
    { family = decoderOnly
    ; srcVocab = param "vocab_size"
    ; tgtVocab = param "vocab_size"
    ; modelDim = param "d_model"
    ; headCount = param "n_heads"
    ; layerCount = param "n_layers"
    ; ffnDim = param "d_ff"
    ; maxLen = param "max_len"
    ; dropout = param "dropout"
    ; constraints = causalMask ∷ []
    }

defaultData : DataIntent
defaultData =
  record
    { datasetVar = "dataset"
    ; inputVar = "x"
    ; targetVar = "y"
    ; taskVar = "task_id"
    ; shape = paired
    ; pipeline = []
    }

defaultTraining : TrainingIntent
defaultTraining =
  record
    { epochs = param "epochs"
    ; learningRate = param "learning_rate"
    ; schedule = constant
    ; optimizer = adam
    ; loss = sparseCategorical
    }

defaultSymbolic : SymbolicIntent
defaultSymbolic =
  record
    { constraints = []
    ; proofObligations = []
    ; notes = []
    }

defaultCoupling : CouplingIntent
defaultCoupling =
  record
    { strategies = []
    ; strength = literal "1.0"
    ; schedule = constant
    ; notes = []
    }

defaultContinual : ContinualTelemetry
defaultContinual =
  record
    { enabled = false
    ; emaAlpha = literal "0.1"
    ; taskVar = "task_id"
    ; bufferVar = "replay_buffer"
    }

defaultTelemetry : TelemetryIntent
defaultTelemetry =
  record
    { signals = []
    ; everySteps = literal "100"
    ; continual = defaultContinual
    }

defaultIntent : EmitIntent
defaultIntent =
  record
    { model = defaultModel
    ; dataIntent = defaultData
    ; training = defaultTraining
    ; telemetry = defaultTelemetry
    ; symbolic = defaultSymbolic
    ; coupling = defaultCoupling
    }
