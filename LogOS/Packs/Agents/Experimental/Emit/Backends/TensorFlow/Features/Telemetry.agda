{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.Features.Telemetry where

open import Data.List using (List; []; _∷_; _++_)
open import Data.String using (String)
open import Data.Bool using (Bool)

open import LogOS.Packs.Agents.Emit.IR.Backend using (Backend)
import LogOS.Packs.Agents.Emit.IR.BackendSyntax as BackendSyntax
import LogOS.Packs.Agents.Emit.IR.Intent as Intent
import LogOS.Packs.Agents.Emit.IR.Features.TelemetryPlan as Plan
open import LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.DataPlan using (DataPlan)
open import LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.Types using (TFTrainingParams)
import LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.SyntaxCore as SyntaxCore

module For (B : Backend) where
  module Py = BackendSyntax.For B
  module TFS = SyntaxCore.For B

  telemetryPlan : TFTrainingParams → DataPlan → Plan.TelemetryPlan
  telemetryPlan t plan =
    Plan.telemetryPlan (TFTrainingParams.telemetry t) (DataPlan.hasTask plan)

  telemetryStepCond : Intent.TelemetryIntent → Py.PyExpr
  telemetryStepCond tel =
    Py.pyBinOp "=="
      (Py.pyBinOp "%" (Py.pyVar "step")
        (tfArgExpr (Intent.TelemetryIntent.everySteps tel)))
      (Py.pyRaw "0")
    where
      tfArgExpr : Intent.EmitArg → Py.PyExpr
      tfArgExpr (Intent.param s) = Py.pyVar s
      tfArgExpr (Intent.literal s) = Py.pyRaw s

  record TelemetryEnv : Set where
    field
      inputVar : Py.PyExpr
      taskVarExpr : Py.PyExpr
      continualActive : Bool
      emaAlpha : Py.PyExpr
      bufferVarName : String
      taskBestIndex : Py.PyExpr
      taskBestMissing : Py.PyExpr

  telemetryEnv : TFTrainingParams → Plan.TelemetryPlan → TelemetryEnv
  telemetryEnv t plan =
    let taskVarExpr = Py.pyVar (TFTrainingParams.taskVar t)
        continual = Plan.TelemetryPlan.continual plan
    in
    record
      { inputVar = Py.pyVar (TFTrainingParams.inputVar t)
      ; taskVarExpr = taskVarExpr
      ; continualActive = Plan.TelemetryPlan.continualActive plan
      ; emaAlpha = tfArgExpr (Intent.ContinualTelemetry.emaAlpha continual)
      ; bufferVarName = Intent.ContinualTelemetry.bufferVar continual
      ; taskBestIndex = Py.pyIndex (Py.pyVar "task_best") taskVarExpr
      ; taskBestMissing = Py.pyBinOp "not in" taskVarExpr (Py.pyVar "task_best")
      }
    where
      tfArgExpr : Intent.EmitArg → Py.PyExpr
      tfArgExpr (Intent.param s) = Py.pyVar s
      tfArgExpr (Intent.literal s) = Py.pyRaw s

  telemetryPrelude : TelemetryEnv → Plan.TelemetryPlan → List Py.PyStmt
  telemetryPrelude env plan =
    let gradPrelude =
          Plan.ifBool (Plan.TelemetryPlan.needGradNorm plan)
            (Py.pyAssign "grad_norm" (TFS.globalNorm (Py.pyVar "grads")) ∷ [])
            []
        timePrelude =
          Plan.ifBool (Plan.TelemetryPlan.needTiming plan)
            ( Py.pyAssign "step_time"
                (Py.pyBinOp "-"
                  TFS.timestamp
                  (Py.pyVar "step_start"))
              ∷ [] )
            []
    in
    gradPrelude ++ timePrelude

  telemetrySignalStmts : TelemetryEnv → Intent.TelemetrySignal → List Py.PyStmt
  telemetrySignalStmts env Intent.lossCurve =
    Py.pyPrint2 (Py.pyString "loss") (Py.pyVar "loss") ∷ []
  telemetrySignalStmts env Intent.gradNorm =
    Py.pyPrint2 (Py.pyString "grad_norm") (Py.pyVar "grad_norm") ∷ []
  telemetrySignalStmts env Intent.stepTime =
    Py.pyPrint2 (Py.pyString "step_time") (Py.pyVar "step_time") ∷ []
  telemetrySignalStmts env Intent.tokensPerSecond =
    Py.pyAssign "tokens"
        (TFS.tfCast
          (TFS.tfSize (TelemetryEnv.inputVar env))
          TFS.float32)
      ∷ Py.pyAssign "tokens_per_sec"
          (Py.pyBinOp "/" (Py.pyVar "tokens") (Py.pyVar "step_time"))
      ∷ Py.pyPrint2 (Py.pyString "tokens_per_sec") (Py.pyVar "tokens_per_sec")
      ∷ []
  telemetrySignalStmts env Intent.taskId =
    Plan.ifBool (TelemetryEnv.continualActive env)
      (Py.pyPrint2 (Py.pyString "task_id") (TelemetryEnv.taskVarExpr env) ∷ [])
      []
  telemetrySignalStmts env Intent.taskLoss =
    Plan.ifBool (TelemetryEnv.continualActive env)
      ( Py.pyExprStmt
          (Py.pyCall (Py.pyVar "print")
            ( Py.pyPos (Py.pyString "task_loss") ∷
              Py.pyPos (TelemetryEnv.taskVarExpr env) ∷
              Py.pyPos (Py.pyVar "loss") ∷
              [] ))
        ∷ [] )
      []
  telemetrySignalStmts env Intent.forgettingProxy =
    Plan.ifBool (TelemetryEnv.continualActive env)
      ( Py.pyIf (TelemetryEnv.taskBestMissing env)
          (Py.pyAssignExpr (TelemetryEnv.taskBestIndex env) (Py.pyVar "loss") ∷ [])
        ∷ Py.pyAssignExpr (TelemetryEnv.taskBestIndex env)
            (Py.pyCall2 (Py.pyVar "min")
              (TelemetryEnv.taskBestIndex env)
              (Py.pyVar "loss"))
        ∷ Py.pyAssign "forgetting"
            (Py.pyBinOp "-" (Py.pyVar "loss") (TelemetryEnv.taskBestIndex env))
        ∷ Py.pyPrint2 (Py.pyString "forgetting") (Py.pyVar "forgetting")
        ∷ [] )
      []
  telemetrySignalStmts env Intent.driftScore =
    Plan.ifBool (TelemetryEnv.continualActive env)
      ( Py.pyAssign "loss_ema"
          (Py.pyBinOp "+"
            (Py.pyBinOp "*" (TelemetryEnv.emaAlpha env) (Py.pyVar "loss"))
            (Py.pyBinOp "*"
              (Py.pyBinOp "-" (Py.pyRaw "1.0") (TelemetryEnv.emaAlpha env))
              (Py.pyVar "loss_ema")))
        ∷ Py.pyAssign "drift"
            (Py.pyBinOp "-" (Py.pyVar "loss") (Py.pyVar "loss_ema"))
        ∷ Py.pyPrint2 (Py.pyString "drift") (Py.pyVar "drift")
        ∷ [] )
      []
  telemetrySignalStmts env Intent.stabilityScore =
    Py.pyAssign "stability"
        (Py.pyBinOp "/"
          (Py.pyVar "loss")
          (Py.pyBinOp "+"
            (Py.pyVar "grad_norm")
            (Py.pyRaw "1e-8")))
      ∷ Py.pyPrint2 (Py.pyString "stability") (Py.pyVar "stability")
      ∷ []
  telemetrySignalStmts env Intent.bufferSize =
    Plan.ifBool (TelemetryEnv.continualActive env)
      ( Py.pyPrint2
          (Py.pyString "buffer_size")
          (Py.pyCall1 (Py.pyVar "len") (Py.pyVar (TelemetryEnv.bufferVarName env)))
        ∷ [] )
      []

  telemetrySignals : TelemetryEnv → List Intent.TelemetrySignal → List Py.PyStmt
  telemetrySignals _ [] = []
  telemetrySignals env (s ∷ ss) =
    telemetrySignalStmts env s ++ telemetrySignals env ss

  telemetryBody : TFTrainingParams → Plan.TelemetryPlan → List Py.PyStmt
  telemetryBody t plan =
    let env = telemetryEnv t plan
        signals = Intent.TelemetryIntent.signals (TFTrainingParams.telemetry t)
    in
    telemetryPrelude env plan ++ telemetrySignals env signals
