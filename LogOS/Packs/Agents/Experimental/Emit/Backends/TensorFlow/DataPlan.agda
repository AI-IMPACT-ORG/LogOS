{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.DataPlan where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.String using (String)

import LogOS.Packs.Agents.Emit.IR.Intent as Intent
open import LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.Types using (TFTrainingParams)

hasShiftRight : List Intent.DataOp → Bool
hasShiftRight [] = false
hasShiftRight (_ ∷ _) = true

dataShapeHasTask : Intent.DataShape → Bool
dataShapeHasTask Intent.taskTokens = true
dataShapeHasTask Intent.taskPaired = true
dataShapeHasTask Intent.tokensOnly = false
dataShapeHasTask Intent.paired = false

dataShapeNeedsPreprocess : Intent.DataShape → List Intent.DataOp → Bool
dataShapeNeedsPreprocess Intent.tokensOnly ops = hasShiftRight ops
dataShapeNeedsPreprocess Intent.taskTokens ops = hasShiftRight ops
dataShapeNeedsPreprocess Intent.paired _ = false
dataShapeNeedsPreprocess Intent.taskPaired _ = false

dataShapeHasTargets : Intent.DataShape → Bool → Bool
dataShapeHasTargets Intent.paired _ = true
dataShapeHasTargets Intent.taskPaired _ = true
dataShapeHasTargets Intent.tokensOnly needsPreprocess = needsPreprocess
dataShapeHasTargets Intent.taskTokens needsPreprocess = needsPreprocess

dataShapeComment : Intent.DataShape → String
dataShapeComment Intent.tokensOnly = "dataset yields tokens"
dataShapeComment Intent.paired = "dataset yields (input, target)"
dataShapeComment Intent.taskTokens = "dataset yields (task, tokens)"
dataShapeComment Intent.taskPaired = "dataset yields (task, input, target)"

record DataPlan : Set where
  field
    hasTask : Bool
    needsPreprocess : Bool
    hasTargets : Bool
    datasetVars : List String
    comment : String

datasetVarsFor : Bool → Bool → TFTrainingParams → List String
datasetVarsFor true true t =
  TFTrainingParams.taskVar t ∷
  TFTrainingParams.inputVar t ∷
  TFTrainingParams.targetVar t ∷
  []
datasetVarsFor true false t =
  TFTrainingParams.taskVar t ∷
  TFTrainingParams.inputVar t ∷
  []
datasetVarsFor false true t =
  TFTrainingParams.inputVar t ∷
  TFTrainingParams.targetVar t ∷
  []
datasetVarsFor false false t =
  TFTrainingParams.inputVar t ∷ []

dataPlan : TFTrainingParams → DataPlan
dataPlan t =
  let shape = TFTrainingParams.dataShape t
      hasTask = dataShapeHasTask shape
      needsPreprocess = dataShapeNeedsPreprocess shape (TFTrainingParams.dataOps t)
      hasTargets = dataShapeHasTargets shape needsPreprocess
  in
  record
    { hasTask = hasTask
    ; needsPreprocess = needsPreprocess
    ; hasTargets = hasTargets
    ; datasetVars = datasetVarsFor hasTask hasTargets t
    ; comment = dataShapeComment shape
    }

needsPreprocess : TFTrainingParams → Bool
needsPreprocess t = DataPlan.needsPreprocess (dataPlan t)

dataHasTask : Intent.DataShape → Bool
dataHasTask = dataShapeHasTask

dataHasTargets : TFTrainingParams → Bool
dataHasTargets t = DataPlan.hasTargets (dataPlan t)

datasetTargets : TFTrainingParams → List String
datasetTargets t = DataPlan.datasetVars (dataPlan t)
