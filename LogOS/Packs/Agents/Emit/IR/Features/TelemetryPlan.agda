{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Emit.IR.Features.TelemetryPlan where

open import LogOS.Prelude.Bool using (Bool; true; false)
open import LogOS.Prelude.List using (List; []; _∷_)
open import LogOS.Prelude.Nat using (ℕ; zero; suc)

import LogOS.Packs.Agents.Emit.IR.Intent as Intent

natEq : ℕ → ℕ → Bool
natEq zero zero = true
natEq zero (suc _) = false
natEq (suc _) zero = false
natEq (suc n) (suc m) = natEq n m

signalTag : Intent.TelemetrySignal → ℕ
signalTag Intent.lossCurve = zero
signalTag Intent.gradNorm = suc zero
signalTag Intent.stepTime = suc (suc zero)
signalTag Intent.tokensPerSecond = suc (suc (suc zero))
signalTag Intent.taskId = suc (suc (suc (suc zero)))
signalTag Intent.taskLoss = suc (suc (suc (suc (suc zero))))
signalTag Intent.forgettingProxy = suc (suc (suc (suc (suc (suc zero)))))
signalTag Intent.driftScore = suc (suc (suc (suc (suc (suc (suc zero))))))
signalTag Intent.stabilityScore =
  suc (suc (suc (suc (suc (suc (suc (suc zero)))))))
signalTag Intent.bufferSize =
  suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))

signalEq : Intent.TelemetrySignal → Intent.TelemetrySignal → Bool
signalEq s1 s2 = natEq (signalTag s1) (signalTag s2)

hasSignal : Intent.TelemetrySignal → List Intent.TelemetrySignal → Bool
hasSignal _ [] = false
hasSignal signal (s ∷ ss) with signalEq signal s
... | true = true
... | false = hasSignal signal ss

record TelemetryFlags : Set where
  field
    lossCurve : Bool
    gradNorm : Bool
    stepTime : Bool
    tokensPerSecond : Bool
    taskId : Bool
    taskLoss : Bool
    forgettingProxy : Bool
    driftScore : Bool
    stabilityScore : Bool
    bufferSize : Bool

telemetryFlags : List Intent.TelemetrySignal → TelemetryFlags
telemetryFlags signals =
  record
    { lossCurve = hasSignal Intent.lossCurve signals
    ; gradNorm = hasSignal Intent.gradNorm signals
    ; stepTime = hasSignal Intent.stepTime signals
    ; tokensPerSecond = hasSignal Intent.tokensPerSecond signals
    ; taskId = hasSignal Intent.taskId signals
    ; taskLoss = hasSignal Intent.taskLoss signals
    ; forgettingProxy = hasSignal Intent.forgettingProxy signals
    ; driftScore = hasSignal Intent.driftScore signals
    ; stabilityScore = hasSignal Intent.stabilityScore signals
    ; bufferSize = hasSignal Intent.bufferSize signals
    }

orBool : Bool → Bool → Bool
orBool true _ = true
orBool false b = b

andBool : Bool → Bool → Bool
andBool true b = b
andBool false _ = false

ifBool : ∀ {A : Set} → Bool → A → A → A
ifBool true x _ = x
ifBool false _ y = y

anySignal : TelemetryFlags → Bool
anySignal flags =
  orBool (TelemetryFlags.lossCurve flags)
    (orBool (TelemetryFlags.gradNorm flags)
      (orBool (TelemetryFlags.stepTime flags)
        (orBool (TelemetryFlags.tokensPerSecond flags)
          (orBool (TelemetryFlags.taskId flags)
            (orBool (TelemetryFlags.taskLoss flags)
              (orBool (TelemetryFlags.forgettingProxy flags)
                (orBool (TelemetryFlags.driftScore flags)
                  (orBool (TelemetryFlags.stabilityScore flags)
                    (TelemetryFlags.bufferSize flags)))))))))

record TelemetryPlan : Set where
  field
    enabled : Bool
    flags : TelemetryFlags
    continual : Intent.ContinualTelemetry
    continualActive : Bool
    needTiming : Bool
    needGradNorm : Bool

telemetryPlan : Intent.TelemetryIntent → Bool → TelemetryPlan
telemetryPlan tel hasTask =
  let signals = Intent.TelemetryIntent.signals tel
      flags = telemetryFlags signals
      continual = Intent.TelemetryIntent.continual tel
      continualActive =
        andBool
          (Intent.ContinualTelemetry.enabled continual)
          hasTask
  in
  record
    { enabled = anySignal flags
    ; flags = flags
    ; continual = continual
    ; continualActive = continualActive
    ; needTiming =
        orBool (TelemetryFlags.stepTime flags)
          (TelemetryFlags.tokensPerSecond flags)
    ; needGradNorm =
        orBool (TelemetryFlags.gradNorm flags)
          (TelemetryFlags.stabilityScore flags)
    }
