{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.Physics.MeasurementExample where

-- Minimal layered measurement slice.
-- - one opacity observation layer forgets hidden state via `decode`,
-- - one `IOPort` telemetry layer chooses what gets asked of that observation,
-- - one adequacy witness relates the layer back to the boundary.

open import LogOS.Prelude
open import LogOS.Host.Nat using (ℕ)
open import LogOS.LT.ConPreorder using (ConPreorder; _⊑_)
open import LogOS.LT.Kernel using (Kernel; bnd; Code; decode; CodePreorder)
open import LogOS.Ports.IO using
  ( IOPort
  ; OutputModel
  ; ModelsOutput
  ; IOAdequacy
  ; constantAdmissibleIOPort
  )
open import LogOS.Ports.Opacity.Port using (OpacityPort)
import LogOS.Ports.Opacity.Port as Opacity

infix 4 _⊑Outcome_

data Outcome : Set where
  coarse : Outcome
  fine   : Outcome

_⊑Outcome_ : Outcome → Outcome → Set
coarse ⊑Outcome coarse = ⊤
coarse ⊑Outcome fine = ⊤
fine ⊑Outcome fine = ⊤
fine ⊑Outcome coarse = ⊥

outcome-refl : ∀ {o} → o ⊑Outcome o
outcome-refl {coarse} = tt
outcome-refl {fine} = tt

outcome-trans : ∀ {a b c} → a ⊑Outcome b → b ⊑Outcome c → a ⊑Outcome c
outcome-trans {coarse} {coarse} {coarse} _ _ = tt
outcome-trans {coarse} {coarse} {fine} _ _ = tt
outcome-trans {coarse} {fine} {coarse} _ ()
outcome-trans {coarse} {fine} {fine} _ _ = tt
outcome-trans {fine} {coarse} {coarse} () _
outcome-trans {fine} {coarse} {fine} () _
outcome-trans {fine} {fine} {coarse} _ ()
outcome-trans {fine} {fine} {fine} _ _ = tt

OutcomePreorder : ConPreorder lzero lzero
OutcomePreorder =
  record
    { Con = Outcome
    ; _⊑_ = _⊑Outcome_
    ; refl = outcome-refl
    ; trans = outcome-trans
    }

MeasurementKernel : Kernel lzero lzero lzero
MeasurementKernel =
  record
    { bnd = OutcomePreorder
    ; Code = Outcome × ℕ
    ; decode = fst
    }

measurement : OpacityPort (Code MeasurementKernel) (bnd MeasurementKernel)
measurement = record { observe = record { μ = decode MeasurementKernel } }

observationLayer : OpacityPort (Code MeasurementKernel) (bnd MeasurementKernel)
observationLayer = measurement

open OpacityPort measurement

data MeasurementInput : Set where
  fullProbe   : MeasurementInput
  coarseProbe : MeasurementInput

measurementTelemetry : IOPort {ℓA = lzero} (Code MeasurementKernel) MeasurementInput (bnd MeasurementKernel)
measurementTelemetry =
  constantAdmissibleIOPort
    (⊤ {ℓ = lzero})
    (λ where
      fullProbe → Opacity.toView measurement
      coarseProbe → record { μ = λ _ → coarse })

telemetryLayer
  : IOPort {ℓA = lzero} (Code MeasurementKernel) MeasurementInput (bnd MeasurementKernel)
telemetryLayer = measurementTelemetry

open IOPort measurementTelemetry using (_⊑io_)

same-outcome-observation
  : ∀ (o : Outcome) (n m : ℕ) → (o , n) ⊑obs (o , m)
same-outcome-observation o n m = outcome-refl

same-outcome-code
  : ∀ (o : Outcome) (n m : ℕ)
  → _⊑_ (CodePreorder MeasurementKernel) (o , n) (o , m)
same-outcome-code o n m = outcome-refl

same-outcome-telemetry
  : ∀ (o : Outcome) (n m : ℕ)
  → (o , n) ⊑io (o , m)
same-outcome-telemetry o n m fullProbe _ = same-outcome-observation o n m
same-outcome-telemetry o n m coarseProbe _ = tt

OutcomeIdentityModel : OutputModel Outcome OutcomePreorder
OutcomeIdentityModel = record { outputs = λ o → o }

OutcomeIdentityAdequacy : IOAdequacy OutcomePreorder (λ _ → ⊤ {ℓ = lzero}) (ModelsOutput OutcomeIdentityModel)
OutcomeIdentityAdequacy =
  record
    { reflect = λ {c} {d} entails → entails d tt outcome-refl
    }

-- This example is intentionally not a `stack2Cat`: it is the smallest useful
-- layered slice, with one observation layer, one telemetry layer, and one
-- adequacy witness.

coarse-refines-fine : _⊑_ OutcomePreorder coarse fine
coarse-refines-fine = tt

not-fine-refines-coarse : ¬ _⊑_ OutcomePreorder fine coarse
not-fine-refines-coarse ()
