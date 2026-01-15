{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.Pipeline where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.String using (String)

import LogOS.Packs.Agents.Emit.IR.Intent as Intent
open import LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.Types
  using (TFEmitSpec; TFTrainingParams)
import LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.DataPlan as DataPlan
import LogOS.Packs.Agents.Emit.IR.Features.TelemetryPlan as Plan
hasCouplingStrategies : List Intent.CouplingStrategy → Bool
hasCouplingStrategies [] = false
hasCouplingStrategies (_ ∷ _) = true

hasSymbolicConstraints : List Intent.SymbolicConstraint → Bool
hasSymbolicConstraints [] = false
hasSymbolicConstraints (_ ∷ _) = true

hasProofObligations : List String → Bool
hasProofObligations [] = false
hasProofObligations (_ ∷ _) = true

orBool : Bool → Bool → Bool
orBool true _ = true
orBool false b = b

hasSymbolic : Intent.SymbolicIntent → Bool
hasSymbolic sym =
  orBool
    (hasSymbolicConstraints (Intent.SymbolicIntent.constraints sym))
    (hasProofObligations (Intent.SymbolicIntent.proofObligations sym))

-- Derived feature flags from the spec (requested usage), not backend capability.
record FeatureCaps : Set where
  field
    telemetry : Bool
    coupling : Bool
    symbolic : Bool

record EmitPlan : Set where
  field
    spec : TFEmitSpec
    dataPlan : DataPlan.DataPlan
    telemetryPlan : Plan.TelemetryPlan
    caps : FeatureCaps

record Pass (A : Set) : Set where
  field
    name : String
    run : A → A

applyPasses : ∀ {A : Set} → List (Pass A) → A → A
applyPasses [] plan = plan
applyPasses (p ∷ ps) plan = applyPasses ps (Pass.run p plan)

seedPlan : TFEmitSpec → EmitPlan
seedPlan spec =
  let train = TFEmitSpec.train spec
      planData = DataPlan.dataPlan train
      telem = Plan.telemetryPlan (TFTrainingParams.telemetry train) (DataPlan.DataPlan.hasTask planData)
      caps =
        record
          { telemetry = Plan.TelemetryPlan.enabled telem
          ; coupling = hasCouplingStrategies (Intent.CouplingIntent.strategies (TFEmitSpec.coupling spec))
          ; symbolic = hasSymbolic (TFEmitSpec.symbolic spec)
          }
  in
  record { spec = spec; dataPlan = planData; telemetryPlan = telem; caps = caps }

passData : Pass EmitPlan
passData =
  record
    { name = "data-plan"
    ; run = λ plan →
        let spec = EmitPlan.spec plan
            planData = DataPlan.dataPlan (TFEmitSpec.train spec)
        in
        record
          { spec = spec
          ; dataPlan = planData
          ; telemetryPlan = EmitPlan.telemetryPlan plan
          ; caps = EmitPlan.caps plan
          }
    }

passTelemetry : Pass EmitPlan
passTelemetry =
  record
    { name = "telemetry-plan"
    ; run = λ plan →
        let spec = EmitPlan.spec plan
            planData = EmitPlan.dataPlan plan
            telem = Plan.telemetryPlan (TFTrainingParams.telemetry (TFEmitSpec.train spec)) (DataPlan.DataPlan.hasTask planData)
        in
        record
          { spec = spec
          ; dataPlan = planData
          ; telemetryPlan = telem
          ; caps = EmitPlan.caps plan
          }
    }

passCaps : Pass EmitPlan
passCaps =
  record
    { name = "feature-caps"
    ; run = λ plan →
        let spec = EmitPlan.spec plan
            telem = EmitPlan.telemetryPlan plan
            caps =
              record
                { telemetry = Plan.TelemetryPlan.enabled telem
                ; coupling =
                    hasCouplingStrategies
                      (Intent.CouplingIntent.strategies (TFEmitSpec.coupling spec))
                ; symbolic = hasSymbolic (TFEmitSpec.symbolic spec)
                }
        in
        record
          { spec = spec
          ; dataPlan = EmitPlan.dataPlan plan
          ; telemetryPlan = telem
          ; caps = caps
          }
    }

defaultPipeline : List (Pass EmitPlan)
defaultPipeline = passData ∷ passTelemetry ∷ passCaps ∷ []

planFromSpec : TFEmitSpec → EmitPlan
planFromSpec spec = applyPasses defaultPipeline (seedPlan spec)
