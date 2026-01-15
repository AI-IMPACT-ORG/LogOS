{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Physics.LearningCost where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature; module LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import Data.Nat using (ℕ; zero; suc)
open import Data.NatOrder using (_≤ℕ_; trans≤ℕ)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; []; _∷_)

open import LogOS.Packs.Agents.Socket.Core using (AgentSocket)
import LogOS.Packs.Agents.Experimental.Physics.MaxwellAgent as Maxwell
import LogOS.Theorems.Meta.LandauerIO as LIO
import LogOS.Domain.Complexity.MeasurementCapacity as MC
import LogOS.Domain.Complexity.DataProcessingInequality as DPI
import LogOS.Domain.Complexity.InfoProcessingBounds as IPB
open import LogOS.Kernel.Graded using (GradedKernel)
import LogOS.Packs.Agents.Learning.SoftPolicy as Soft

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

  record LearningAssumptions : Set (lsuc (lsuc ℓ)) where
    field
      landauer : LandauerForSocket
      Learns : Cosp → Set ℓ
      learns→merges
        : ∀ f → Learns f → LIO.LandauerIOAssumptions.MergesIO landauer f

  learning-cost-lower-bound
    : (A : LearningAssumptions)
    → ∀ f → LearningAssumptions.Learns A f
    → QAdapter._≤s_ Q
        (LIO.LandauerIOAssumptions.L (LearningAssumptions.landauer A))
        (LIO.LandauerIOAssumptions.cost (LearningAssumptions.landauer A) f)
  learning-cost-lower-bound A f pr =
    LIO.landauer-io boundaryIO (LearningAssumptions.landauer A) f
      (LearningAssumptions.learns→merges A f pr)

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

  record MaxwellLearningAssumptions : Set (lsuc (lsuc ℓ)) where
    field
      landauer : LandauerForSocket
      condensation : CondensationAssumptions
      Learns : Cosp → Set ℓ
      learns→merges
        : ∀ f → Learns f → LIO.LandauerIOAssumptions.MergesIO landauer f

  learning-from-maxwell
    : MaxwellLearningAssumptions
    → LearningAssumptions
  learning-from-maxwell A = record
    { landauer = MaxwellLearningAssumptions.landauer A
    ; Learns = MaxwellLearningAssumptions.Learns A
    ; learns→merges = MaxwellLearningAssumptions.learns→merges A
    }

  maxwell-learning-cost
    : (A : MaxwellLearningAssumptions)
    → ∀ f → MaxwellLearningAssumptions.Learns A f
    → QAdapter._≤s_ Q
        (LIO.LandauerIOAssumptions.L (MaxwellLearningAssumptions.landauer A))
        (LIO.LandauerIOAssumptions.cost (MaxwellLearningAssumptions.landauer A) f)
  maxwell-learning-cost A f pr =
    learning-cost-lower-bound (learning-from-maxwell A) f pr

  maxwell-learning-condensation
    : (A : MaxwellLearningAssumptions)
    → ∀ (C : DPI.Channel Cosp) (f : Cosp)
    → MaxwellLearningAssumptions.Learns A f
    → MC.MeasurementCapacity.info (CondensationAssumptions.capacity (MaxwellLearningAssumptions.condensation A))
        (DPI.Channel.run C f)
      ≤ℕ
      MC.mul
        (MC.MeasurementCapacity.κ (CondensationAssumptions.capacity (MaxwellLearningAssumptions.condensation A)))
        (MC.MeasurementCapacity.meas (CondensationAssumptions.capacity (MaxwellLearningAssumptions.condensation A)) f)
  maxwell-learning-condensation A C f _ =
    condensation-bound (MaxwellLearningAssumptions.condensation A) C f

  maxwell-universal-learning-cost
    : (A : MaxwellLearningAssumptions) (U : UniversalEval)
    → ∀ f → MaxwellLearningAssumptions.Learns A (UniversalEval.eval U f)
    → QAdapter._≤s_ Q
        (LIO.LandauerIOAssumptions.L (MaxwellLearningAssumptions.landauer A))
        (LIO.LandauerIOAssumptions.cost (MaxwellLearningAssumptions.landauer A)
          (UniversalEval.eval U f))
  maxwell-universal-learning-cost A U f pr =
    universal-learning-cost (learning-from-maxwell A) U f pr

  maxwell-learning-summary
    : (A : MaxwellLearningAssumptions)
    → ∀ (C : DPI.Channel Cosp) (f : Cosp)
    → MaxwellLearningAssumptions.Learns A f
    → QAdapter._≤s_ Q
        (LIO.LandauerIOAssumptions.L (MaxwellLearningAssumptions.landauer A))
        (LIO.LandauerIOAssumptions.cost (MaxwellLearningAssumptions.landauer A) f)
      ×
      MC.MeasurementCapacity.info (CondensationAssumptions.capacity (MaxwellLearningAssumptions.condensation A))
        (DPI.Channel.run C f)
        ≤ℕ
      MC.mul
        (MC.MeasurementCapacity.κ (CondensationAssumptions.capacity (MaxwellLearningAssumptions.condensation A)))
        (MC.MeasurementCapacity.meas (CondensationAssumptions.capacity (MaxwellLearningAssumptions.condensation A)) f)
  maxwell-learning-summary A C f pr =
    maxwell-learning-cost A f pr , maxwell-learning-condensation A C f pr

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

    module L = Soft.For K
    open L using (SoftUpdate)

    record SoftLearningAssumptions : Set (lsuc (lsuc ℓ)) where
      field
        landauer : LandauerForSocket
        stepProgram : ∀ {g} → SoftUpdate g → Cosp
        Learns : Cosp → Set ℓ
        learns→merges
          : ∀ f → Learns f → LIO.LandauerIOAssumptions.MergesIO landauer f
        stepLearns : ∀ {g} (s : SoftUpdate g) → Learns (stepProgram s)

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

    record SoftLearningCondensationAssumptions : Set (lsuc (lsuc ℓ)) where
      field
        condensation : CondensationAssumptions
        stepProgram : ∀ {g} → SoftUpdate g → Cosp

    soft-learning-condensation
      : (A : SoftLearningCondensationAssumptions)
      → ∀ {g} (C : DPI.Channel Cosp) (s : SoftUpdate g)
      → MC.MeasurementCapacity.info (CondensationAssumptions.capacity (SoftLearningCondensationAssumptions.condensation A))
          (DPI.Channel.run C (SoftLearningCondensationAssumptions.stepProgram A s))
        ≤ℕ
        MC.mul
          (MC.MeasurementCapacity.κ (CondensationAssumptions.capacity (SoftLearningCondensationAssumptions.condensation A)))
          (MC.MeasurementCapacity.meas (CondensationAssumptions.capacity (SoftLearningCondensationAssumptions.condensation A))
            (SoftLearningCondensationAssumptions.stepProgram A s))
    soft-learning-condensation A C s =
      condensation-bound
        (SoftLearningCondensationAssumptions.condensation A)
        C
        (SoftLearningCondensationAssumptions.stepProgram A s)

    record SoftLearningThroughputAssumptions : Set (lsuc (lsuc ℓ)) where
      field
        landauer : LandauerForSocket
        throughput : IPB.ThroughputAssumptions Sig Q
        stepProgram : ∀ {g} → SoftUpdate g → Cosp
        Learns : Cosp → Set ℓ
        learns→merges
          : ∀ f → Learns f → LIO.LandauerIOAssumptions.MergesIO landauer f
        stepLearns : ∀ {g} (s : SoftUpdate g) → Learns (stepProgram s)

    soft-learning-from-throughput
      : SoftLearningThroughputAssumptions
      → SoftLearningAssumptions
    soft-learning-from-throughput A = record
      { landauer = SoftLearningThroughputAssumptions.landauer A
      ; stepProgram = SoftLearningThroughputAssumptions.stepProgram A
      ; Learns = SoftLearningThroughputAssumptions.Learns A
      ; learns→merges = SoftLearningThroughputAssumptions.learns→merges A
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
