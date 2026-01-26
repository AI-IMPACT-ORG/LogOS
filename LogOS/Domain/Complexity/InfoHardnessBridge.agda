{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.InfoHardnessBridge where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import LogOS.Prelude.Nat using (ℕ)
open import LogOS.Prelude.Product using (Σ; _,_; proj₁; proj₂)

open import LogOS.Prelude.NatOrder using (_≤ℕ_; trans≤ℕ)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Kernel.Graded
import LogOS.Domain.Complexity.MeasurementCapacity as MC
import LogOS.Domain.Complexity.TruthRoute_Grade_Only as TRG

-- Generic (model-polymorphic) info-hardness bridge --------------------------
--
-- The bridge only depends on:
-- - an input type,
-- - a size measure,
-- - a polynomial predicate,
-- - and a deterministic bound relation DetWithin.

module Generic
  {ℓI ℓP ℓD : Level}
  (Input : Set ℓI)
  (Size : Input → ℕ)
  (IsPoly : (ℕ → ℕ) → Set ℓP)
  (DetWithin : ℕ → Input → Set ℓD)
  where

  -- Deterministic bottleneck interface:
  -- running within time t forces an upper bound on “needed information”.
  record DetBottleneck : Set (ℓI ⊔ ℓD) where
    field
      κ      : ℕ
      need   : Input → ℕ
      budget : ℕ → ℕ

      detNeed≤budget
        : ∀ {t} (x : Input)
          → DetWithin t x
          → need x ≤ℕ MC.mul κ (budget t)

  -- “Information hardness” premise phrased to compose with the bottleneck:
  -- for every polynomial time bound, some input requires more information than
  -- any t = p(size x) run could supply.
  InfoHardness : DetBottleneck → Set (ℓI ⊔ ℓP)
  InfoHardness B =
    ∀ (p : ℕ → ℕ) → IsPoly p →
      Σ Input (λ x →
        ¬ (DetBottleneck.need B x ≤ℕ MC.mul (DetBottleneck.κ B) (DetBottleneck.budget B (p (Size x)))))

  -- Physically aligned axioms: “minimum information density” + “super-poly volume”.
  --
  -- 1) `MinInfoDensity`: there is a smallest non-trivial information density
  --    per resolved cell (e.g., per uncertainty-limited measurement bin).
  -- 2) `SuperPolyResolution`: some inputs require super-polynomial total
  --    resolution volume at that density relative to any polynomial budget.
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
         : Set (ℓI ⊔ ℓP) where
    field
      superpolyResolution : ∀ (p : ℕ → ℕ) → IsPoly p →
        Σ Input (λ x →
          ¬ (MC.mul density (resolutionCells x) ≤ℕ
              MC.mul (DetBottleneck.κ B) (DetBottleneck.budget B (p (Size x)))))

  infoHardnessFromDensityAxioms
    : ∀ {B : DetBottleneck}
      → (D : MinInfoDensity B)
      → SuperPolyResolution B (MinInfoDensity.density D) (MinInfoDensity.resolutionCells D)
      → InfoHardness B
  infoHardnessFromDensityAxioms D hard p polyP =
    let ex = SuperPolyResolution.superpolyResolution hard p polyP in
    let x  = proj₁ ex in
    x , λ need≤ ->
          proj₂ ex (trans≤ℕ (MinInfoDensity.density≤need D x) need≤)

  -- Super-polynomial hardness of the deterministic time relation.
  SuperPolyHardness : Set (ℓI ⊔ ℓP ⊔ ℓD)
  SuperPolyHardness =
    ∀ (p : ℕ → ℕ) → IsPoly p →
      Σ Input (λ x → ¬ (DetWithin (p (Size x)) x))

  -- Derived: information hardness implies TruthRoute-style SuperPolyHardness.
  detSuperPolyFromInfo
    : ∀ (B : DetBottleneck) → InfoHardness B → SuperPolyHardness
  detSuperPolyFromInfo B IH p polyP =
    let ex = IH p polyP in
    let x  = proj₁ ex in
    x , λ within →
          proj₂ ex
            (DetBottleneck.detNeed≤budget B x within)

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

  record DetBottleneck : Set (ℓI ⊔ ℓD ⊔ ℓG) where
    field
      κ      : ℕ
      need   : Input → ℕ
      budget : Grade → ℕ

      detNeed≤budget
        : ∀ {g} (x : Input)
          → DetWithinAt g x
          → need x ≤ℕ MC.mul κ (budget g)

  InfoHardness : DetBottleneck → Set (ℓI ⊔ ℓP)
  InfoHardness B =
    ∀ (p : ℕ → ℕ) → IsPoly p →
      Σ Input (λ x →
        ¬ (DetBottleneck.need B x ≤ℕ
            MC.mul (DetBottleneck.κ B)
              (DetBottleneck.budget B (gradeBound (p (Size x))))))

  -- Physically aligned axioms: “minimum information density” + “super-poly volume”.
  record MinInfoDensity (B : DetBottleneck) : Set (ℓI ⊔ ℓD ⊔ ℓG) where
    field
      density : ℕ
      resolutionCells : Input → ℕ
      density≤need : ∀ x →
        MC.mul density (resolutionCells x) ≤ℕ DetBottleneck.need B x

  record SuperPolyResolution
         (B : DetBottleneck)
         (density : ℕ)
         (resolutionCells : Input → ℕ)
         : Set (ℓI ⊔ ℓP ⊔ ℓG) where
    field
      superpolyResolution : ∀ (p : ℕ → ℕ) → IsPoly p →
        Σ Input (λ x →
          ¬ (MC.mul density (resolutionCells x) ≤ℕ
              MC.mul (DetBottleneck.κ B)
                (DetBottleneck.budget B (gradeBound (p (Size x))))))

  infoHardnessFromDensityAxioms
    : ∀ {B : DetBottleneck}
      → (D : MinInfoDensity B)
      → SuperPolyResolution B (MinInfoDensity.density D) (MinInfoDensity.resolutionCells D)
      → InfoHardness B
  infoHardnessFromDensityAxioms D hard p polyP =
    let ex = SuperPolyResolution.superpolyResolution hard p polyP in
    let x  = proj₁ ex in
    x , λ need≤ ->
          proj₂ ex (trans≤ℕ (MinInfoDensity.density≤need D x) need≤)

  SuperPolyHardness : Set (ℓI ⊔ ℓP ⊔ ℓD)
  SuperPolyHardness =
    ∀ (p : ℕ → ℕ) → IsPoly p →
      Σ Input (λ x → ¬ (DetWithinAt (gradeBound (p (Size x))) x))

  detSuperPolyFromInfo
    : ∀ (B : DetBottleneck) → InfoHardness B → SuperPolyHardness
  detSuperPolyFromInfo B IH p polyP =
    let ex = IH p polyP in
    let x  = proj₁ ex in
    x , λ within →
          proj₂ ex
            (DetBottleneck.detNeed≤budget B x within)

-- Grade-native polynomial bounds: no `gradeBound` in the statement.

module GenericGradePoly
  {ℓI ℓP ℓD ℓG : Level}
  (Input : Set ℓI)
  (Size : Input → ℕ)
  (Grade : Set ℓG)
  (IsPolyG : (ℕ → Grade) → Set ℓP)
  (DetWithinAt : Grade → Input → Set ℓD)
  where

  record DetBottleneck : Set (ℓI ⊔ ℓD ⊔ ℓG) where
    field
      κ      : ℕ
      need   : Input → ℕ
      budget : Grade → ℕ

      detNeed≤budget
        : ∀ {g} (x : Input)
          → DetWithinAt g x
          → need x ≤ℕ MC.mul κ (budget g)

  InfoHardness : DetBottleneck → Set (ℓI ⊔ ℓP ⊔ ℓG)
  InfoHardness B =
    ∀ (g : ℕ → Grade) → IsPolyG g →
      Σ Input (λ x →
        ¬ (DetBottleneck.need B x ≤ℕ
            MC.mul (DetBottleneck.κ B)
              (DetBottleneck.budget B (g (Size x)))))

  -- Physically aligned axioms: “minimum information density” + “super-poly volume”.
  record MinInfoDensity (B : DetBottleneck) : Set (ℓI ⊔ ℓD ⊔ ℓG) where
    field
      density : ℕ
      resolutionCells : Input → ℕ
      density≤need : ∀ x →
        MC.mul density (resolutionCells x) ≤ℕ DetBottleneck.need B x

  record SuperPolyResolution
         (B : DetBottleneck)
         (density : ℕ)
         (resolutionCells : Input → ℕ)
         : Set (ℓI ⊔ ℓP ⊔ ℓG) where
    field
      superpolyResolution : ∀ (g : ℕ → Grade) → IsPolyG g →
        Σ Input (λ x →
          ¬ (MC.mul density (resolutionCells x) ≤ℕ
              MC.mul (DetBottleneck.κ B)
                (DetBottleneck.budget B (g (Size x)))))

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

  SuperPolyHardness : Set (ℓI ⊔ ℓP ⊔ ℓD ⊔ ℓG)
  SuperPolyHardness =
    ∀ (g : ℕ → Grade) → IsPolyG g →
      Σ Input (λ x → ¬ (DetWithinAt (g (Size x)) x))

  detSuperPolyFromInfo
    : ∀ (B : DetBottleneck) → InfoHardness B → SuperPolyHardness
  detSuperPolyFromInfo B IH g polyG =
    let ex = IH g polyG in
    let x  = proj₁ ex in
    x , λ within →
          proj₂ ex
            (DetBottleneck.detNeed≤budget B x within)

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
