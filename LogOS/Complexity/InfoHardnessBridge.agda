{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Complexity.InfoHardnessBridge where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import LogOS.Prelude using (ℕ)
open import LogOS.Prelude using (Σ; _,_; proj₁; proj₂)

open import LogOS.Prelude.NatOrder using (_≤ℕ_; trans≤ℕ)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.API.Kernel.Graded
import LogOS.Complexity.MeasurementCapacity as MC
import LogOS.Complexity.TruthRoute_Grade_Only as TRG

-- Generic (model-polymorphic) info-hardness bridge --------------------------
--
-- The bridge only depends on:
-- - an input type,
-- - a size measure,
-- - a polynomial predicate,
-- - and a deterministic bound relation DetWithin.

module GenericIndexed
  {ℓI ℓP ℓD ℓPI ℓBI : Level}
  (Input : Set ℓI)
  (Size : Input → ℕ)
  (PolyIndex : Set ℓPI)
  (BudgetIndex : Set ℓBI)
  (IsPolyIndex : (ℕ → PolyIndex) → Set ℓP)
  (toBudgetIndex : (ℕ → PolyIndex) → ℕ → BudgetIndex)
  (DetWithinAt : BudgetIndex → Input → Set ℓD)
  where

  -- Deterministic bottleneck interface:
  -- running within budget index i forces an upper bound on needed information.
  record DetBottleneck : Set (ℓI ⊔ ℓD ⊔ ℓBI) where
    field
      κ      : ℕ
      need   : Input → ℕ
      budget : BudgetIndex → ℕ

      detNeed≤budget
        : ∀ {i} (x : Input)
          → DetWithinAt i x
          → need x ≤ℕ MC.mul κ (budget i)

  -- “Information hardness” premise phrased to compose with the bottleneck:
  -- for every polynomial budget family, some input requires more information.
  InfoHardness : DetBottleneck → Set (ℓI ⊔ ℓP ⊔ ℓPI)
  InfoHardness B =
    ∀ (g : ℕ → PolyIndex) → IsPolyIndex g →
      Σ Input (λ x →
        ¬ (DetBottleneck.need B x ≤ℕ
            MC.mul (DetBottleneck.κ B)
              (DetBottleneck.budget B (toBudgetIndex g (Size x)))))

  -- Physically aligned axioms: “minimum information density” + “super-poly volume”.
  record MinInfoDensity (B : DetBottleneck) : Set (ℓI ⊔ ℓD) where
    field
      density : ℕ
      resolutionCells : Input → ℕ
      density≤need : ∀ x →
        MC.mul density (resolutionCells x) ≤ℕ DetBottleneck.need B x

  record SuperPolyResolution
         (B : DetBottleneck)
         (density : ℕ)
         (resolutionCells : Input → ℕ)
         : Set (ℓI ⊔ ℓP ⊔ ℓPI) where
    field
      superpolyResolution : ∀ (g : ℕ → PolyIndex) → IsPolyIndex g →
        Σ Input (λ x →
          ¬ (MC.mul density (resolutionCells x) ≤ℕ
              MC.mul (DetBottleneck.κ B)
                (DetBottleneck.budget B (toBudgetIndex g (Size x)))))

  infoHardnessFromDensityAxioms
    : ∀ {B : DetBottleneck}
      → (D : MinInfoDensity B)
      → SuperPolyResolution B (MinInfoDensity.density D) (MinInfoDensity.resolutionCells D)
      → InfoHardness B
  infoHardnessFromDensityAxioms D hard g polyG =
    let ex = SuperPolyResolution.superpolyResolution hard g polyG in
    let x  = proj₁ ex in
    x , λ need≤ ->
          proj₂ ex (trans≤ℕ (MinInfoDensity.density≤need D x) need≤)

  -- Super-polynomial hardness of the deterministic bound relation.
  SuperPolyHardness : Set (ℓI ⊔ ℓP ⊔ ℓD ⊔ ℓPI)
  SuperPolyHardness =
    ∀ (g : ℕ → PolyIndex) → IsPolyIndex g →
      Σ Input (λ x → ¬ (DetWithinAt (toBudgetIndex g (Size x)) x))

  -- Derived: information hardness implies TruthRoute-style SuperPolyHardness.
  detSuperPolyFromInfo
    : ∀ (B : DetBottleneck) → InfoHardness B → SuperPolyHardness
  detSuperPolyFromInfo B IH g polyG =
    let ex = IH g polyG in
    let x  = proj₁ ex in
    x , λ within →
          proj₂ ex
            (DetBottleneck.detNeed≤budget B x within)

module Generic
  {ℓI ℓP ℓD : Level}
  (Input : Set ℓI)
  (Size : Input → ℕ)
  (IsPoly : (ℕ → ℕ) → Set ℓP)
  (DetWithin : ℕ → Input → Set ℓD)
  where
  module I = GenericIndexed Input Size ℕ ℕ IsPoly (λ p n → p n) DetWithin
  open I public
    using
      ( DetBottleneck
      ; InfoHardness
      ; MinInfoDensity
      ; SuperPolyResolution
      ; infoHardnessFromDensityAxioms
      ; SuperPolyHardness
      ; detSuperPolyFromInfo
      )

-- Grade-indexed info-hardness bridge ----------------------------------------

module GenericGrade
  {ℓI ℓP ℓD ℓG : Level}
  (Input : Set ℓI)
  (Size : Input → ℕ)
  (IsPoly : (ℕ → ℕ) → Set ℓP)
  (Grade : Set ℓG)
  (DetWithinAt : Grade → Input → Set ℓD)
  (gradeBound : ℕ → Grade)
  where
  module I =
    GenericIndexed Input Size ℕ Grade IsPoly
      (λ p n → gradeBound (p n))
      DetWithinAt
  open I public
    using
      ( DetBottleneck
      ; InfoHardness
      ; MinInfoDensity
      ; SuperPolyResolution
      ; infoHardnessFromDensityAxioms
      ; SuperPolyHardness
      ; detSuperPolyFromInfo
      )

-- Grade-native polynomial bounds: no `gradeBound` in the statement.

module GenericGradePoly
  {ℓI ℓP ℓD ℓG : Level}
  (Input : Set ℓI)
  (Size : Input → ℕ)
  (Grade : Set ℓG)
  (IsPolyG : (ℕ → Grade) → Set ℓP)
  (DetWithinAt : Grade → Input → Set ℓD)
  where
  module I =
    GenericIndexed Input Size Grade Grade IsPolyG
      (λ g n → g n)
      DetWithinAt
  open I public
    using
      ( DetBottleneck
      ; InfoHardness
      ; MinInfoDensity
      ; SuperPolyResolution
      ; infoHardnessFromDensityAxioms
      ; SuperPolyHardness
      ; detSuperPolyFromInfo
      )

-- Bridge: specialize the generic bottleneck to a graded-kernel truth route.

module For
  {ℓ ℓI ℓP ℓA : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (Input : Set ℓI)
  (Size  : Input → ℕ)
  (DetRun : Input → GradedKernel.Code K)
  (VerRun : Input → GradedKernel.Code K)
  (VerRunWith : Input → GradedKernel.Code K → GradedKernel.Code K)
  (IsPoly : (ℕ → ℕ) → Set ℓP)
  (gradeBound : ℕ → QAdapter.Scale Q)
  (Acc : ConPreorder.Con (BulkBoundary.bnd (GradedKernel.BB K)) → Set ℓA)
  where

  module R = TRG.UniformNatFromRuns K Input Size DetRun VerRun VerRunWith IsPoly gradeBound
  module G = Generic Input Size IsPoly (R.DetWithin Acc)

  open G public
    using
      ( DetBottleneck
      ; InfoHardness
      ; MinInfoDensity
      ; SuperPolyResolution
      ; infoHardnessFromDensityAxioms
      ; detSuperPolyFromInfo
      )

module ForGrade
  {ℓ ℓI ℓP ℓA : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (Input : Set ℓI)
  (Size  : Input → ℕ)
  (DetRun : Input → GradedKernel.Code K)
  (VerRun : Input → GradedKernel.Code K)
  (VerRunWith : Input → GradedKernel.Code K → GradedKernel.Code K)
  (IsPoly : (ℕ → ℕ) → Set ℓP)
  (gradeBound : ℕ → QAdapter.Scale Q)
  (Acc : ConPreorder.Con (BulkBoundary.bnd (GradedKernel.BB K)) → Set ℓA)
  where

  module R = TRG.UniformNatFromRuns K Input Size DetRun VerRun VerRunWith IsPoly gradeBound
  module G = GenericGrade Input Size IsPoly R.Grade (R.DetWithinAt Acc) gradeBound

  open G public
    using
      ( DetBottleneck
      ; InfoHardness
      ; MinInfoDensity
      ; SuperPolyResolution
      ; infoHardnessFromDensityAxioms
      ; detSuperPolyFromInfo
      ; SuperPolyHardness
      )
