{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Physics.LearningCost where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature; module LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Boundary.Telemetry using (TelemetryTrace; ProgramTelemetryPort)
open import LogOS.Ports.Semantic.SatMor using (SatRefinement₀; sat-→₀)
open import LogOS.Prelude using (ℕ; zero; suc)
open import LogOS.Prelude.NatOrder using (_≤ℕ_; trans≤ℕ)
open import LogOS.Prelude using (Σ; _×_; _,_)
open import LogOS.Prelude.List using (List; []; _∷_)

open import LogOS.Packs.Agents.Socket.Core using (AgentSocket)
import LogOS.Packs.Agents.Experimental.Physics.MaxwellAgent as Maxwell
import LogOS.Theorems.Meta.LandauerIO as LIO
import LogOS.Complexity.MeasurementCapacity as MC
import LogOS.Complexity.SecondLaw as SL
import LogOS.Complexity.LCUToLandauer as LCU
import LogOS.Complexity.DataProcessingInequality as DPI
import LogOS.Complexity.InfoProcessingBounds as IPB
open import LogOS.Kernel.Graded using (GradedKernel)
import LogOS.Packs.Agents.Learning.SoftPolicy as Soft
import LogOS.Packs.Agents.Learning.Core as LearningCore

-- Capstone theorems: learning is possible, but any learning event costs energy.
-- Universal evaluation inherits the same lower bound.

module For
  {ℓ ℓTask : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  {Task : Set ℓTask}
  (Sock : AgentSocket Sig Q Task)
  where

  open AgentSocket Sock
  open LogOSSignature Sig using (Cosp)

  module MX = Maxwell.For Sock
  open MX using (LandauerForSocket)
  module L = LearningCore.For Sock
  open L using (LearningStep)

  record LearningAssumptions : Set (lsuc (lsuc ℓ)) where
    field
      landauer : LandauerForSocket
      Learns : Cosp → Set ℓ
      learns-ref : SatRefinement₀ Cosp
                    (λ _ f → Learns f)
                    (λ _ f → LIO.LandauerIOAssumptions.MergesIO landauer f)

    learns→merges
      : ∀ f → Learns f → LIO.LandauerIOAssumptions.MergesIO landauer f
    learns→merges f pr = sat-→₀ learns-ref f pr

  learning-cost-lower-bound
    : (A : LearningAssumptions)
    → ∀ f → LearningAssumptions.Learns A f
    → QAdapter._≤s_ Q
        (LIO.LandauerIOAssumptions.L (LearningAssumptions.landauer A))
        (LIO.LandauerIOAssumptions.cost (LearningAssumptions.landauer A) f)
  learning-cost-lower-bound A f pr =
    LIO.landauer-io boundaryIO (LearningAssumptions.landauer A) f
      (LearningAssumptions.learns→merges A f pr)

  record EntropyAssumptions : Set (lsuc (lsuc ℓ)) where
    field
      secondLaw : SL.SecondLawAssumptions Sig Q
      Learns : Cosp → Set ℓ
      learns-ref : SatRefinement₀ Cosp
                    (λ _ f → Learns f)
                    (λ _ f → LCU.Merges (SL.SecondLawAssumptions.LCUA secondLaw) f)

    learns→merges
      : ∀ f → Learns f
        → LCU.Merges (SL.SecondLawAssumptions.LCUA secondLaw) f
    learns→merges f pr = sat-→₀ learns-ref f pr

  learning-entropy-increase
    : (A : EntropyAssumptions)
    → ∀ f → EntropyAssumptions.Learns A f
    → Σ (LCU.LCUObsAssumptions.Obs (SL.SecondLawAssumptions.LCUA (EntropyAssumptions.secondLaw A)))
        (λ x →
          QAdapter._≤s_ Q
            (QAdapter._·_ Q
              (SL.SecondLawAssumptions.Entropy (EntropyAssumptions.secondLaw A) x)
              (LCU.LCUObsAssumptions.L (SL.SecondLawAssumptions.LCUA (EntropyAssumptions.secondLaw A))))
            (SL.SecondLawAssumptions.Entropy (EntropyAssumptions.secondLaw A)
              (LCU.LCUObsAssumptions.act (SL.SecondLawAssumptions.LCUA (EntropyAssumptions.secondLaw A)) f x)))
  learning-entropy-increase A f pr =
    SL.merge→entropy+ (EntropyAssumptions.secondLaw A) f
      (EntropyAssumptions.learns→merges A f pr)

  record UniversalEval : Set (lsuc ℓ) where
    field
      eval : Cosp → Cosp

  universal-learning-cost
    : (A : LearningAssumptions) (U : UniversalEval)
    → ∀ f → LearningAssumptions.Learns A (UniversalEval.eval U f)
    → QAdapter._≤s_ Q
        (LIO.LandauerIOAssumptions.L (LearningAssumptions.landauer A))
        (LIO.LandauerIOAssumptions.cost (LearningAssumptions.landauer A)
          (UniversalEval.eval U f))
  universal-learning-cost A U f pr =
    learning-cost-lower-bound A (UniversalEval.eval U f) pr

  record CondensationAssumptions : Set (lsuc (lsuc ℓ)) where
    field
      capacity : MC.MeasurementCapacity Sig Q
      dpi : ∀ (C : DPI.Channel Cosp) (f : Cosp)
            → MC.MeasurementCapacity.info capacity (DPI.Channel.run C f)
              ≤ℕ
              MC.MeasurementCapacity.info capacity f

  record CondensationFromTelemetry {ℓT : Level} (T : TelemetryTrace ℓT)
                                  : Set (lsuc (lsuc (ℓ ⊔ ℓT))) where
    field
      capacity : MC.MeasurementCapacity Sig Q
      telemetry : ProgramTelemetryPort
        Sig Q _ _ _ boundaryIO T
      bridge : MC.TelemetryCapacityBridge
        Sig Q boundaryIO T telemetry capacity
      traceInfoMono
        : MC.TraceInfoMono T (MC.TelemetryCapacityBridge.trace→info bridge)
      contract
        : ∀ (C : DPI.Channel Cosp) (f : Cosp)
        → TelemetryTrace._⊑T_ T
            (ProgramTelemetryPort.observe-∂ telemetry
              (LogOSSignature.to∂ Sig (DPI.Channel.run C f)))
            (ProgramTelemetryPort.observe-∂ telemetry
              (LogOSSignature.to∂ Sig f))

  condensation-from-telemetry
    : ∀ {ℓT} {T : TelemetryTrace ℓT}
    → CondensationFromTelemetry T
    → CondensationAssumptions
  condensation-from-telemetry {T = T} A =
    record
      { capacity = CondensationFromTelemetry.capacity A
      ; dpi = MC.dpiFromTelemetry
          boundaryIO T
          (CondensationFromTelemetry.telemetry A)
          (CondensationFromTelemetry.capacity A)
          (CondensationFromTelemetry.bridge A)
          (CondensationFromTelemetry.traceInfoMono A)
          (CondensationFromTelemetry.contract A)
      }

  condensation-bound
    : (A : CondensationAssumptions)
    → ∀ (C : DPI.Channel Cosp) (f : Cosp)
    → MC.MeasurementCapacity.info (CondensationAssumptions.capacity A)
        (DPI.Channel.run C f)
      ≤ℕ
      MC.mul
        (MC.MeasurementCapacity.κ (CondensationAssumptions.capacity A))
        (MC.MeasurementCapacity.meas (CondensationAssumptions.capacity A) f)
  condensation-bound A C f =
    let open CondensationAssumptions A
        open MC.MeasurementCapacity capacity
    in trans≤ℕ (dpi C f) (info≤κ·meas f)

  record MaxwellLearningAssumptions {ℓT : Level} (T : TelemetryTrace ℓT)
    : Set (lsuc (lsuc (ℓ ⊔ ℓT))) where
    field
      landauer : LandauerForSocket
      condensation : CondensationFromTelemetry T
      Learns : Cosp → Set ℓ
      learns-ref : SatRefinement₀ Cosp
                    (λ _ f → Learns f)
                    (λ _ f → LIO.LandauerIOAssumptions.MergesIO landauer f)

    learns→merges
      : ∀ f → Learns f → LIO.LandauerIOAssumptions.MergesIO landauer f
    learns→merges f pr = sat-→₀ learns-ref f pr

  maxwell-condensation
    : ∀ {ℓT} {T : TelemetryTrace ℓT}
    → MaxwellLearningAssumptions T
    → CondensationAssumptions
  maxwell-condensation A =
    condensation-from-telemetry (MaxwellLearningAssumptions.condensation A)

  learning-from-maxwell
    : ∀ {ℓT} {T : TelemetryTrace ℓT}
    → MaxwellLearningAssumptions T
    → LearningAssumptions
  learning-from-maxwell A = record
    { landauer = MaxwellLearningAssumptions.landauer A
    ; Learns = MaxwellLearningAssumptions.Learns A
    ; learns-ref = MaxwellLearningAssumptions.learns-ref A
    }

  maxwell-learning-cost
    : ∀ {ℓT} {T : TelemetryTrace ℓT}
    → (A : MaxwellLearningAssumptions T)
    → ∀ f → MaxwellLearningAssumptions.Learns A f
    → QAdapter._≤s_ Q
        (LIO.LandauerIOAssumptions.L (MaxwellLearningAssumptions.landauer A))
        (LIO.LandauerIOAssumptions.cost (MaxwellLearningAssumptions.landauer A) f)
  maxwell-learning-cost A f pr =
    learning-cost-lower-bound (learning-from-maxwell A) f pr

  maxwell-learning-condensation
    : ∀ {ℓT} {T : TelemetryTrace ℓT}
    → (A : MaxwellLearningAssumptions T)
    → ∀ (C : DPI.Channel Cosp) (f : Cosp)
    → MaxwellLearningAssumptions.Learns A f
    → MC.MeasurementCapacity.info (CondensationAssumptions.capacity (maxwell-condensation A))
        (DPI.Channel.run C f)
      ≤ℕ
      MC.mul
        (MC.MeasurementCapacity.κ (CondensationAssumptions.capacity (maxwell-condensation A)))
        (MC.MeasurementCapacity.meas (CondensationAssumptions.capacity (maxwell-condensation A)) f)
  maxwell-learning-condensation A C f _ =
    condensation-bound (maxwell-condensation A) C f

  maxwell-universal-learning-cost
    : ∀ {ℓT} {T : TelemetryTrace ℓT}
    → (A : MaxwellLearningAssumptions T) (U : UniversalEval)
    → ∀ f → MaxwellLearningAssumptions.Learns A (UniversalEval.eval U f)
    → QAdapter._≤s_ Q
        (LIO.LandauerIOAssumptions.L (MaxwellLearningAssumptions.landauer A))
        (LIO.LandauerIOAssumptions.cost (MaxwellLearningAssumptions.landauer A)
          (UniversalEval.eval U f))
  maxwell-universal-learning-cost A U f pr =
    universal-learning-cost (learning-from-maxwell A) U f pr

  maxwell-learning-summary
    : ∀ {ℓT} {T : TelemetryTrace ℓT}
    → (A : MaxwellLearningAssumptions T)
    → ∀ (C : DPI.Channel Cosp) (f : Cosp)
    → MaxwellLearningAssumptions.Learns A f
    → QAdapter._≤s_ Q
        (LIO.LandauerIOAssumptions.L (MaxwellLearningAssumptions.landauer A))
        (LIO.LandauerIOAssumptions.cost (MaxwellLearningAssumptions.landauer A) f)
      ×
      MC.MeasurementCapacity.info (CondensationAssumptions.capacity (maxwell-condensation A))
        (DPI.Channel.run C f)
        ≤ℕ
      MC.mul
        (MC.MeasurementCapacity.κ (CondensationAssumptions.capacity (maxwell-condensation A)))
        (MC.MeasurementCapacity.meas (CondensationAssumptions.capacity (maxwell-condensation A)) f)
  maxwell-learning-summary A C f pr =
    maxwell-learning-cost A f pr , maxwell-learning-condensation A C f pr

  -- -----------------------------------------------------------------------
  -- Step-level bridges: learning updates as programs.
  -- -----------------------------------------------------------------------

  record StepLearningAssumptions : Set (lsuc (lsuc ℓ)) where
    field
      learning : LearningAssumptions
      stepProg : LearningStep → Cosp
      stepLearns : ∀ s → LearningAssumptions.Learns learning (stepProg s)

  step-learning-cost
    : (A : StepLearningAssumptions)
    → ∀ s
    → QAdapter._≤s_ Q
        (LIO.LandauerIOAssumptions.L (LearningAssumptions.landauer (StepLearningAssumptions.learning A)))
        (LIO.LandauerIOAssumptions.cost
          (LearningAssumptions.landauer (StepLearningAssumptions.learning A))
          (StepLearningAssumptions.stepProg A s))
  step-learning-cost A s =
    learning-cost-lower-bound (StepLearningAssumptions.learning A)
      (StepLearningAssumptions.stepProg A s)
      (StepLearningAssumptions.stepLearns A s)

  record StepEntropyAssumptions : Set (lsuc (lsuc ℓ)) where
    field
      entropy : EntropyAssumptions
      stepProg : LearningStep → Cosp
      stepLearns : ∀ s → EntropyAssumptions.Learns entropy (stepProg s)

  step-learning-entropy
    : (A : StepEntropyAssumptions)
    → ∀ s
    → Σ (LCU.LCUObsAssumptions.Obs
          (SL.SecondLawAssumptions.LCUA
            (EntropyAssumptions.secondLaw (StepEntropyAssumptions.entropy A))))
        (λ x →
          QAdapter._≤s_ Q
            (QAdapter._·_ Q
              (SL.SecondLawAssumptions.Entropy
                (EntropyAssumptions.secondLaw (StepEntropyAssumptions.entropy A)) x)
              (LCU.LCUObsAssumptions.L
                (SL.SecondLawAssumptions.LCUA
                  (EntropyAssumptions.secondLaw (StepEntropyAssumptions.entropy A)))))
            (SL.SecondLawAssumptions.Entropy
              (EntropyAssumptions.secondLaw (StepEntropyAssumptions.entropy A))
              (LCU.LCUObsAssumptions.act
                (SL.SecondLawAssumptions.LCUA
                  (EntropyAssumptions.secondLaw (StepEntropyAssumptions.entropy A)))
                (StepEntropyAssumptions.stepProg A s) x)))
  step-learning-entropy A s =
    learning-entropy-increase (StepEntropyAssumptions.entropy A)
      (StepEntropyAssumptions.stepProg A s)
      (StepEntropyAssumptions.stepLearns A s)

  record StepMaxwellLearningAssumptions {ℓT : Level} (T : TelemetryTrace ℓT)
    : Set (lsuc (lsuc (ℓ ⊔ ℓT))) where
    field
      maxwell : MaxwellLearningAssumptions T
      stepProg : LearningStep → Cosp
      stepLearns : ∀ s → MaxwellLearningAssumptions.Learns maxwell (stepProg s)

  step-maxwell-learning-cost
    : ∀ {ℓT} {T : TelemetryTrace ℓT}
    → (A : StepMaxwellLearningAssumptions T)
    → ∀ s
    → QAdapter._≤s_ Q
        (LIO.LandauerIOAssumptions.L
          (MaxwellLearningAssumptions.landauer (StepMaxwellLearningAssumptions.maxwell A)))
        (LIO.LandauerIOAssumptions.cost
          (MaxwellLearningAssumptions.landauer (StepMaxwellLearningAssumptions.maxwell A))
          (StepMaxwellLearningAssumptions.stepProg A s))
  step-maxwell-learning-cost A s =
    maxwell-learning-cost (StepMaxwellLearningAssumptions.maxwell A)
      (StepMaxwellLearningAssumptions.stepProg A s)
      (StepMaxwellLearningAssumptions.stepLearns A s)

  step-maxwell-learning-condensation
    : ∀ {ℓT} {T : TelemetryTrace ℓT}
    → (A : StepMaxwellLearningAssumptions T)
    → ∀ (C : DPI.Channel Cosp) s
    → MC.MeasurementCapacity.info
        (CondensationAssumptions.capacity
          (maxwell-condensation
            (StepMaxwellLearningAssumptions.maxwell A)))
        (DPI.Channel.run C (StepMaxwellLearningAssumptions.stepProg A s))
      ≤ℕ
      MC.mul
        (MC.MeasurementCapacity.κ
          (CondensationAssumptions.capacity
            (maxwell-condensation
              (StepMaxwellLearningAssumptions.maxwell A))))
        (MC.MeasurementCapacity.meas
          (CondensationAssumptions.capacity
            (maxwell-condensation
              (StepMaxwellLearningAssumptions.maxwell A)))
          (StepMaxwellLearningAssumptions.stepProg A s))
  step-maxwell-learning-condensation A C s =
    maxwell-learning-condensation (StepMaxwellLearningAssumptions.maxwell A)
      C (StepMaxwellLearningAssumptions.stepProg A s)
      (StepMaxwellLearningAssumptions.stepLearns A s)

  blackbox-eval-bound
    : (A : CondensationAssumptions)
    → ∀ (C : DPI.Channel Cosp) (f : Cosp)
    → MC.MeasurementCapacity.info (CondensationAssumptions.capacity A)
        (DPI.Channel.run C f)
      ≤ℕ
      MC.mul
        (MC.MeasurementCapacity.κ (CondensationAssumptions.capacity A))
        (MC.MeasurementCapacity.meas (CondensationAssumptions.capacity A) f)
  blackbox-eval-bound = condensation-bound

  learning-condensation-bound
    : (A : CondensationAssumptions)
    → (Learns : Cosp → Set ℓ)
    → ∀ (C : DPI.Channel Cosp) (f : Cosp)
    → Learns f
    → MC.MeasurementCapacity.info (CondensationAssumptions.capacity A)
        (DPI.Channel.run C f)
      ≤ℕ
      MC.mul
        (MC.MeasurementCapacity.κ (CondensationAssumptions.capacity A))
        (MC.MeasurementCapacity.meas (CondensationAssumptions.capacity A) f)
  learning-condensation-bound A _ C f _ = condensation-bound A C f

  -- -----------------------------------------------------------------------
  -- Training traces: list of learning steps + composition cost bound.
  -- -----------------------------------------------------------------------

  All : ∀ {ℓA} {A : Set ℓA} → (A → Set ℓ) → List A → Set (ℓA ⊔ ℓ)
  All P [] = ⊤
  All P (x ∷ xs) = P x × All P xs

  len : ∀ {ℓA} {A : Set ℓA} → List A → ℕ
  len [] = zero
  len (_ ∷ xs) = suc (len xs)

  powS : QAdapter.Scale Q → ℕ → QAdapter.Scale Q
  powS x zero = QAdapter.e Q
  powS x (suc n) = QAdapter._·_ Q x (powS x n)

  record TrainingTrace : Set (lsuc ℓ) where
    field
      base  : LogOSSignature.Iface Sig
      steps : List Cosp

  compList : LogOSSignature.Iface Sig → List Cosp → Cosp
  compList base [] = LogOSSignature.idC Sig base
  compList base (f ∷ fs) = LogOSSignature._∘C_ Sig (compList base fs) f

  costList
    : (A : LearningAssumptions)
    → List Cosp → QAdapter.Scale Q
  costList A [] = QAdapter.e Q
  costList A (f ∷ fs) =
    QAdapter._·_ Q
      (LIO.LandauerIOAssumptions.cost (LearningAssumptions.landauer A) f)
      (costList A fs)

  costList≤comp
    : (A : LearningAssumptions)
    → ∀ base fs
    → QAdapter._≤s_ Q (costList A fs)
        (LIO.LandauerIOAssumptions.cost (LearningAssumptions.landauer A)
          (compList base fs))
  costList≤comp A base [] =
    LIO.LandauerIOAssumptions.cost-id (LearningAssumptions.landauer A) base
  costList≤comp A base (f ∷ fs) =
    let open QAdapter Q
        land = LearningAssumptions.landauer A
        step₁ : _≤s_ (costList A (f ∷ fs))
                    (_·_ (LIO.LandauerIOAssumptions.cost land f)
                         (LIO.LandauerIOAssumptions.cost land (compList base fs)))
        step₁ = ·-mono (≤s-refl {a = LIO.LandauerIOAssumptions.cost land f})
                       (costList≤comp A base fs)
        step₂ =
          LIO.LandauerIOAssumptions.cost-comp land f (compList base fs)
    in ≤s-trans step₁ step₂

  powS≤costList
    : (A : LearningAssumptions)
    → ∀ fs → All (LearningAssumptions.Learns A) fs
    → QAdapter._≤s_ Q
        (powS (LIO.LandauerIOAssumptions.L (LearningAssumptions.landauer A)) (len fs))
        (costList A fs)
  powS≤costList A [] _ =
    QAdapter.≤s-refl Q
  powS≤costList A (f ∷ fs) (lf , lfs) =
    let open QAdapter Q
        land = LearningAssumptions.landauer A
        L = LIO.LandauerIOAssumptions.L land
        step₁ : _≤s_ (powS L (suc (len fs)))
                    (_·_ (LIO.LandauerIOAssumptions.cost land f) (costList A fs))
        step₁ = ·-mono
                  (learning-cost-lower-bound A f lf)
                  (powS≤costList A fs lfs)
    in step₁

  training-energy-bound
    : (A : LearningAssumptions)
    → (T : TrainingTrace)
    → All (LearningAssumptions.Learns A) (TrainingTrace.steps T)
    → QAdapter._≤s_ Q
        (powS (LIO.LandauerIOAssumptions.L (LearningAssumptions.landauer A))
          (len (TrainingTrace.steps T)))
        (LIO.LandauerIOAssumptions.cost (LearningAssumptions.landauer A)
          (compList (TrainingTrace.base T) (TrainingTrace.steps T)))
  training-energy-bound A T learns =
    QAdapter.≤s-trans Q
      (powS≤costList A (TrainingTrace.steps T) learns)
      (costList≤comp A (TrainingTrace.base T) (TrainingTrace.steps T))

  throughput-bound
    : (T : IPB.ThroughputAssumptions Sig Q)
    → ∀ f
    → IPB._≤ℕ_
        (IPB.ThroughputAssumptions.merges T f)
        (IPB.ThroughputAssumptions.budget T (IPB.ThroughputAssumptions.ticks T f))
  throughput-bound T f = IPB.ThroughputAssumptions.merges≤budget T f

  learning-throughput-bound
    : (T : IPB.ThroughputAssumptions Sig Q)
    → (Learns : Cosp → Set ℓ)
    → ∀ f → Learns f
    → IPB._≤ℕ_
        (IPB.ThroughputAssumptions.merges T f)
        (IPB.ThroughputAssumptions.budget T (IPB.ThroughputAssumptions.ticks T f))
  learning-throughput-bound T _ f _ = throughput-bound T f

  module Graded (K : GradedKernel Sig Q) where

    module SoftL = Soft.For K
    open SoftL using (SoftUpdate)

    record SoftLearningAssumptions : Set (lsuc (lsuc ℓ)) where
      field
        landauer : LandauerForSocket
        stepProgram : ∀ {g} → SoftUpdate g → Cosp
        Learns : Cosp → Set ℓ
        learns-ref : SatRefinement₀ Cosp
                      (λ _ f → Learns f)
                      (λ _ f → LIO.LandauerIOAssumptions.MergesIO landauer f)
        stepLearns : ∀ {g} (s : SoftUpdate g) → Learns (stepProgram s)

      learns→merges
        : ∀ f → Learns f → LIO.LandauerIOAssumptions.MergesIO landauer f
      learns→merges f pr = sat-→₀ learns-ref f pr

    soft-learning-cost
      : (A : SoftLearningAssumptions)
      → ∀ {g} (s : SoftUpdate g)
      → QAdapter._≤s_ Q
          (LIO.LandauerIOAssumptions.L (SoftLearningAssumptions.landauer A))
          (LIO.LandauerIOAssumptions.cost (SoftLearningAssumptions.landauer A)
            (SoftLearningAssumptions.stepProgram A s))
    soft-learning-cost A s =
      LIO.landauer-io boundaryIO (SoftLearningAssumptions.landauer A)
        (SoftLearningAssumptions.stepProgram A s)
        (SoftLearningAssumptions.learns→merges A _ (SoftLearningAssumptions.stepLearns A s))

    record SoftLearningCondensationAssumptions {ℓT : Level} (T : TelemetryTrace ℓT)
      : Set (lsuc (lsuc (ℓ ⊔ ℓT))) where
      field
        condensation : CondensationFromTelemetry T
        stepProgram : ∀ {g} → SoftUpdate g → Cosp

    soft-condensation
      : ∀ {ℓT} {T : TelemetryTrace ℓT}
      → SoftLearningCondensationAssumptions T
      → CondensationAssumptions
    soft-condensation A =
      condensation-from-telemetry (SoftLearningCondensationAssumptions.condensation A)

    soft-learning-condensation
      : ∀ {ℓT} {T : TelemetryTrace ℓT}
      → (A : SoftLearningCondensationAssumptions T)
      → ∀ {g} (C : DPI.Channel Cosp) (s : SoftUpdate g)
      → MC.MeasurementCapacity.info (CondensationAssumptions.capacity (soft-condensation A))
          (DPI.Channel.run C (SoftLearningCondensationAssumptions.stepProgram A s))
        ≤ℕ
        MC.mul
          (MC.MeasurementCapacity.κ (CondensationAssumptions.capacity (soft-condensation A)))
          (MC.MeasurementCapacity.meas (CondensationAssumptions.capacity (soft-condensation A))
            (SoftLearningCondensationAssumptions.stepProgram A s))
    soft-learning-condensation A C s =
      condensation-bound
        (soft-condensation A)
        C
        (SoftLearningCondensationAssumptions.stepProgram A s)

    record SoftLearningThroughputAssumptions : Set (lsuc (lsuc ℓ)) where
      field
        landauer : LandauerForSocket
        throughput : IPB.ThroughputAssumptions Sig Q
        stepProgram : ∀ {g} → SoftUpdate g → Cosp
        Learns : Cosp → Set ℓ
        learns-ref : SatRefinement₀ Cosp
                      (λ _ f → Learns f)
                      (λ _ f → LIO.LandauerIOAssumptions.MergesIO landauer f)
        stepLearns : ∀ {g} (s : SoftUpdate g) → Learns (stepProgram s)

      learns→merges
        : ∀ f → Learns f → LIO.LandauerIOAssumptions.MergesIO landauer f
      learns→merges f pr = sat-→₀ learns-ref f pr

    soft-learning-from-throughput
      : SoftLearningThroughputAssumptions
      → SoftLearningAssumptions
    soft-learning-from-throughput A = record
      { landauer = SoftLearningThroughputAssumptions.landauer A
      ; stepProgram = SoftLearningThroughputAssumptions.stepProgram A
      ; Learns = SoftLearningThroughputAssumptions.Learns A
      ; learns-ref = SoftLearningThroughputAssumptions.learns-ref A
      ; stepLearns = SoftLearningThroughputAssumptions.stepLearns A
      }

    soft-learning-summary
      : (A : SoftLearningThroughputAssumptions)
      → ∀ {g} (s : SoftUpdate g)
      → QAdapter._≤s_ Q
          (LIO.LandauerIOAssumptions.L (SoftLearningThroughputAssumptions.landauer A))
          (LIO.LandauerIOAssumptions.cost (SoftLearningThroughputAssumptions.landauer A)
            (SoftLearningThroughputAssumptions.stepProgram A s))
        ×
        IPB._≤ℕ_
          (IPB.ThroughputAssumptions.merges (SoftLearningThroughputAssumptions.throughput A)
            (SoftLearningThroughputAssumptions.stepProgram A s))
          (IPB.ThroughputAssumptions.budget (SoftLearningThroughputAssumptions.throughput A)
            (IPB.ThroughputAssumptions.ticks (SoftLearningThroughputAssumptions.throughput A)
              (SoftLearningThroughputAssumptions.stepProgram A s)))
    soft-learning-summary A s =
      let costBound =
            soft-learning-cost (soft-learning-from-throughput A) s
          tp = SoftLearningThroughputAssumptions.throughput A
          thrBound =
            IPB.ThroughputAssumptions.merges≤budget tp
              (SoftLearningThroughputAssumptions.stepProgram A s)
      in costBound , thrBound
