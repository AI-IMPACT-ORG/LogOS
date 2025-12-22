{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.InfoBottleneckAdaptersGraded where

open import LogOS.Prelude
open import Data.Nat using (ℕ)
open import Data.NatOrder using (_≤ℕ_; trans≤ℕ)

open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Domain.Complexity.Poly using (PolyPred)
import LogOS.Domain.Universality.MeasurementCapacity as MC
import LogOS.Domain.Complexity.InfoHardnessBridge as IHB
import LogOS.Domain.Complexity.InfoBottleneckAdaptersG as IBG
import LogOS.Domain.Complexity.ResourceSchemaGraded as RS
import LogOS.Domain.Complexity.ObservabilityBudgetGraded as OB

private
  detNeed≤budgetAux
    : {ℓI ℓD ℓB ℓQ ℓQD : Level}
      {Input : Set ℓI}
      {Q : QAdapter ℓQ}
      {Bound : Set ℓB}
      (boundToGrade : Bound → QAdapter.Scale Q)
      (DetWithinAt : Bound → Input → Set ℓD)
      {QD : Set ℓQD}
      (time : QD → Input → QAdapter.Scale Q)
      (meas : QD → Input → ℕ)
      (κ : ℕ)
      (need : Input → ℕ)
      (budget : QAdapter.Scale Q → ℕ)
      (monoBudget : ∀ {t u} → QAdapter._≤s_ Q t u → budget t ≤ℕ budget u)
      (need≤κ·meas : (qd : QD) → (x : Input) → need x ≤ℕ MC.mul κ (meas qd x))
      (meas≤budget : (qd : QD) → (x : Input) → meas qd x ≤ℕ budget (time qd x))
      (qd : QD)
      (time≤ : ∀ {b} (x : Input) → DetWithinAt b x →
               QAdapter._≤s_ Q (time qd x) (boundToGrade b))
      {b : Bound}
      (x : Input)
      → DetWithinAt b x
      → need x ≤ℕ MC.mul κ (budget (boundToGrade b))
  detNeed≤budgetAux boundToGrade DetWithinAt time meas κ need budget monoBudget need≤κ·meas meas≤budget qd time≤ x within =
    let
      meas≤budget-time = meas≤budget qd x
      meas≤budget-b =
        trans≤ℕ
          meas≤budget-time
          (monoBudget (time≤ x within))
      need≤κ·meas' = need≤κ·meas qd x
    in
    trans≤ℕ need≤κ·meas' (MC.monoMul κ meas≤budget-b)

-- Graded adapters that connect LOB packs to the generic info-hardness interface.

module FromLOB
  {ℓI ℓP ℓD ℓQ : Level}
  (Input : Set ℓI)
  (Size : Input → ℕ)
  (IsPoly : (ℕ → ℕ) → Set ℓP)
  (DetWithin : ℕ → Input → Set ℓD)
  (Pℕ : PolyPred)
  (Q : QAdapter ℓQ)
  (gradeBound : ℕ → QAdapter.Scale Q)
  where

  open QAdapter Q renaming (_≤s_ to _≤g_)

  module G = IHB.Generic Input Size IsPoly DetWithin
  open G public using (DetBottleneck)

  module R = RS.For {ℓI = ℓI} {ℓ = ℓD} {ℓQ = ℓQ} Input Size Pℕ Q gradeBound
  module O = OB.For {ℓI = ℓI} {ℓ = ℓD} {ℓQ = ℓQ} Input Size Pℕ Q gradeBound

  record DetRunAsQTime : Set (lsuc (lsuc (ℓI ⊔ ℓD ⊔ ℓQ))) where
    field
      L  : R.Language
      QD : R.QTimeDecider L
      time≤ : ∀ {t} (x : Input) →
              DetWithin t x → _≤g_ (R.QTimeDecider.time QD x) (gradeBound t)

  detBottleneck : (lob : O.LOB) → DetRunAsQTime → DetBottleneck
  detBottleneck lob dr =
    record
      { κ      = O.LOB.κ lob
      ; need   = O.LOB.need lob
      ; budget = λ t → O.LOB.budget lob (gradeBound t)
      ; detNeed≤budget =
          λ {t} x within →
            let open DetRunAsQTime dr in
            detNeed≤budgetAux {Input = Input} {Q = Q} {Bound = ℕ}
              gradeBound
              DetWithin
              R.QTimeDecider.time
              R.QTimeDecider.meas
              (O.LOB.κ lob)
              (O.LOB.need lob)
              (O.LOB.budget lob)
              (O.LOB.monoBudget lob)
              (λ qd y → O.LOB.need≤κ·meas lob qd y)
              (λ qd y → O.LOB.meas≤budget lob qd y)
              QD
              time≤
              x
              within
      }

-- Grade-indexed variant: budgets live directly in the grade.

module FromLOBGrade
  {ℓI ℓP ℓD ℓQ : Level}
  (Input : Set ℓI)
  (Size : Input → ℕ)
  (IsPoly : (ℕ → ℕ) → Set ℓP)
  (Pℕ : PolyPred)
  (Q : QAdapter ℓQ)
  (DetWithinAt : QAdapter.Scale Q → Input → Set ℓD)
  (gradeBound : ℕ → QAdapter.Scale Q)
  where

  open QAdapter Q renaming (_≤s_ to _≤g_; Scale to Grade)

  module G = IHB.GenericGrade Input Size IsPoly Grade DetWithinAt gradeBound
  open G public using (DetBottleneck)

  module R = RS.For {ℓI = ℓI} {ℓ = ℓD} {ℓQ = ℓQ} Input Size Pℕ Q gradeBound
  module O = OB.For {ℓI = ℓI} {ℓ = ℓD} {ℓQ = ℓQ} Input Size Pℕ Q gradeBound

  record DetRunAsQTime : Set (lsuc (lsuc (ℓI ⊔ ℓD ⊔ ℓQ))) where
    field
      L  : R.Language
      QD : R.QTimeDecider L
      time≤ : ∀ {g} (x : Input) →
              DetWithinAt g x → _≤g_ (R.QTimeDecider.time QD x) g

  detBottleneck : (lob : O.LOB) → DetRunAsQTime → DetBottleneck
  detBottleneck lob dr =
    record
      { κ      = O.LOB.κ lob
      ; need   = O.LOB.need lob
      ; budget = O.LOB.budget lob
      ; detNeed≤budget =
          λ {g} x within →
            let open DetRunAsQTime dr in
            detNeed≤budgetAux {Input = Input} {Q = Q} {Bound = Grade}
              (λ g → g)
              DetWithinAt
              R.QTimeDecider.time
              R.QTimeDecider.meas
              (O.LOB.κ lob)
              (O.LOB.need lob)
              (O.LOB.budget lob)
              (O.LOB.monoBudget lob)
              (λ qd y → O.LOB.need≤κ·meas lob qd y)
              (λ qd y → O.LOB.meas≤budget lob qd y)
              QD
              time≤
              x
              within
      }

-- Grade-indexed + grade-bound decider variant (QTimeDeciderG).

module FromLOBGradeG
  {ℓI ℓP ℓD ℓQ : Level}
  (Input : Set ℓI)
  (Size : Input → ℕ)
  (IsPoly : (ℕ → ℕ) → Set ℓP)
  (Pℕ : PolyPred)
  (Q : QAdapter ℓQ)
  (DetWithinAt : QAdapter.Scale Q → Input → Set ℓD)
  (gradeBound : ℕ → QAdapter.Scale Q)
  where

  open QAdapter Q renaming (_≤s_ to _≤g_; Scale to Grade)

  module G = IHB.GenericGrade Input Size IsPoly Grade DetWithinAt gradeBound
  open G public using (DetBottleneck)

  module R = RS.For {ℓI = ℓI} {ℓ = ℓD} {ℓQ = ℓQ} Input Size Pℕ Q gradeBound
  module O = OB.For {ℓI = ℓI} {ℓ = ℓD} {ℓQ = ℓQ} Input Size Pℕ Q gradeBound

  record DetRunAsQTimeG : Set (lsuc (lsuc (ℓI ⊔ ℓD ⊔ ℓQ))) where
    field
      L  : R.Language
      QD : R.QTimeDeciderG L
      time≤ : ∀ {g} (x : Input) →
              DetWithinAt g x → _≤g_ (R.QTimeDeciderG.time QD x) g

  detBottleneck : (lob : O.LOBG) → DetRunAsQTimeG → DetBottleneck
  detBottleneck lob dr =
    record
      { κ      = O.LOBG.κ lob
      ; need   = O.LOBG.need lob
      ; budget = O.LOBG.budget lob
      ; detNeed≤budget =
          λ {g} x within →
            let open DetRunAsQTimeG dr in
            detNeed≤budgetAux {Input = Input} {Q = Q} {Bound = Grade}
              (λ g → g)
              DetWithinAt
              R.QTimeDeciderG.time
              R.QTimeDeciderG.meas
              (O.LOBG.κ lob)
              (O.LOBG.need lob)
              (O.LOBG.budget lob)
              (O.LOBG.monoBudget lob)
              (λ qd y → O.LOBG.need≤κ·meas lob qd y)
              (λ qd y → O.LOBG.meas≤budget lob qd y)
              QD
              time≤
              x
              within
      }

-- Grade-native polynomial bounds (no `gradeBound` in the bottleneck interface).

module FromLOBGradePG
  {ℓI ℓD ℓQ ℓPG : Level}
  (Input : Set ℓI)
  (Size : Input → ℕ)
  (Q : QAdapter ℓQ)
  (IsPolyG : (ℕ → QAdapter.Scale Q) → Set ℓPG)
  (DetWithinAt : QAdapter.Scale Q → Input → Set ℓD)
  where

  module Core = IBG.FromLOB Input Size Q IsPolyG DetWithinAt
  open Core public
