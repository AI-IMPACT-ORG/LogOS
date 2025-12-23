{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.PhysProofBridgeWGraded where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.NatOrder using (_≤ℕ_)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Kernel.Graded
open import LogOS.Domain.Complexity.Poly using (PolyPred)
import LogOS.Domain.Complexity.PhysicsClassesWGraded as PCW
import LogOS.Domain.Complexity.TruthRoute as TR
import LogOS.Domain.Complexity.TruthRoute_Grade_Only as TRG
import LogOS.Domain.Complexity.PolyGrade as PG

-- Proof-theory + Landauer-style plumbing for PhysP (grade-native):
-- exactly like the ℕ version, but cost bounds live in the grade.

module For {ℓI ℓW ℓ ℓQ : Level}
           (Input : Set ℓI)
           (size  : Input → ℕ)
           (Pℕ    : PolyPred)
           (Q     : QAdapter ℓQ)
           (gradeBound : ℕ → QAdapter.Scale Q)
           where

  open QAdapter Q renaming (Scale to Grade; _≤s_ to _≤g_)

  module C = PCW.For {ℓI = ℓI} {ℓW = ℓW} {ℓ = ℓ} {ℓQ = ℓQ} Input size Pℕ Q gradeBound

  Language = C.Language

  record MergeMeasure (L : Language) : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
    field
      merges : C.PhysDecider L → Input → ℕ
      merges≤cost : ∀ (PD : C.PhysDecider L) (x : Input) →
                      _≤g_ (gradeBound (merges PD x)) (C.PhysDecider.cost PD x)

  record ProofLowerBound (L : Language) (MM : MergeMeasure L)
    : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
    field
      superPolyMerges : ∀ (PD : C.PhysDecider L) →
        Σ Input (λ x → ¬ (_≤g_ (gradeBound (MergeMeasure.merges MM PD x))
                            (gradeBound (C.PhysDecider.bound PD (size x)))))

  SuperPolyCostDet : Language → Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ)))
  SuperPolyCostDet L =
    ∀ (PD : C.PhysDecider L) →
      Σ Input (λ x → ¬ (_≤g_ (C.PhysDecider.cost PD x)
                          (gradeBound (C.PhysDecider.bound PD (size x)))))

  superPolyCostFromProof
    : ∀ {L} (MM : MergeMeasure L)
      → ProofLowerBound L MM
      → SuperPolyCostDet L
  superPolyCostFromProof {L = L} MM PLB PD =
    let ex = ProofLowerBound.superPolyMerges PLB PD in
    let x  = proj₁ ex in
    x , λ cost≤ →
          proj₂ ex (QAdapter.≤s-trans Q (MergeMeasure.merges≤cost MM PD x) cost≤)

-- Kernel-native proof bridge (TruthRoute-based).
-- Convert proof lower bounds into TruthRoute super-poly hardness.

module Kernel
  {ℓ ℓI ℓP : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (Input : Set ℓI)
  (Size : Input → ℕ)
  (DetRun : Input → GradedKernel.Code K)
  (VerRun : Input → GradedKernel.Code K)
  (VerRunWith : Input → GradedKernel.Code K → GradedKernel.Code K)
  (IsPoly : (ℕ → ℕ) → Set ℓP)
  (gradeBound : ℕ → QAdapter.Scale Q)
  (WSize : GradedKernel.Code K → ℕ)
  where

  module R = TR.For K Input Size DetRun VerRun VerRunWith IsPoly gradeBound
  module C = PCW.Kernel K Input Size DetRun VerRun VerRunWith IsPoly gradeBound WSize

  open C public using (Con; PhysP; PhysNPw; SuperPolyHardness; notPhysP)

  record MergeMeasure {ℓA} (Acc : Con → Set ℓA)
    : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓP ⊔ ℓA))) where
    field
      merges : Input → ℕ
      merges≤bound : ∀ {t x} → R.DetWithin Acc t x → merges x ≤ℕ t

  record ProofLowerBound {ℓA} (Acc : Con → Set ℓA) (MM : MergeMeasure Acc)
    : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓP ⊔ ℓA))) where
    field
      superPolyMerges : ∀ (p : ℕ → ℕ) → IsPoly p →
        Σ Input (λ x → ¬ (MergeMeasure.merges MM x ≤ℕ p (Size x)))

  superPolyHardnessFromProof
    : ∀ {ℓA} {Acc : Con → Set ℓA}
      (MM : MergeMeasure Acc)
      → ProofLowerBound Acc MM
      → SuperPolyHardness Acc
  superPolyHardnessFromProof MM PLB p polyP =
    let ex = ProofLowerBound.superPolyMerges PLB p polyP in
    let x  = proj₁ ex in
    x , λ within →
          proj₂ ex (MergeMeasure.merges≤bound MM within)

-- Kernel-native proof bridge (TruthRoute_Grade_Only-based).
-- Grade polynomials live in `PolyPredG`; merge bounds are taken via a grade budget.

module KernelG
  {ℓ ℓI : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (Input : Set ℓI)
  (Size : Input → ℕ)
  (DetRun : Input → GradedKernel.Code K)
  (VerRun : Input → GradedKernel.Code K)
  (VerRunWith : Input → GradedKernel.Code K → GradedKernel.Code K)
  (PGG : PG.PolyPredG (QAdapter.Scale Q))
  (Pℕ : PolyPred)
  (WSize : GradedKernel.Code K → ℕ)
  where

  module R = TRG.For K Input Size DetRun VerRun VerRunWith
  module C = PCW.KernelG K Input Size DetRun VerRun VerRunWith PGG Pℕ WSize

  open C public using (Con; PhysP; PhysNPw; SuperPolyHardness; notPhysP)

  record MergeMeasure {ℓA} (Acc : Con → Set ℓA)
    : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓA))) where
    field
      budget : R.Grade → ℕ
      merges : Input → ℕ
      merges≤budget : ∀ {g x} → R.DetWithinAt Acc g x → merges x ≤ℕ budget g

  record ProofLowerBound {ℓA} (Acc : Con → Set ℓA) (MM : MergeMeasure Acc)
    : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓA))) where
    field
      superPolyMerges : ∀ (g : ℕ → R.Grade) →
        PG.PolyPredG.isPolyG PGG g →
        Σ Input (λ x → ¬ (MergeMeasure.merges MM x ≤ℕ
                          MergeMeasure.budget MM (g (Size x))))

  superPolyHardnessFromProof
    : ∀ {ℓA} {Acc : Con → Set ℓA}
      (MM : MergeMeasure Acc)
      → ProofLowerBound Acc MM
      → SuperPolyHardness Acc
  superPolyHardnessFromProof MM PLB g polyG =
    let ex = ProofLowerBound.superPolyMerges PLB g polyG in
    let x  = proj₁ ex in
    x , λ within →
          proj₂ ex (MergeMeasure.merges≤budget MM within)
