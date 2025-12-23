{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.PhysProofBridgeWCostGuardsGraded where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; proj₁; proj₂)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Kernel.Graded
open import LogOS.Domain.Complexity.Poly using (PolyPred)
import LogOS.Domain.Complexity.PhysicsClassesWCostGuardsGraded as PCWCG
import LogOS.Domain.Complexity.PhysProofBridgeWGraded as PBW
import LogOS.Domain.Complexity.PolyGrade as PG

-- Proof-theory + Landauer-style plumbing for the cost-guard witness-size classes:
-- grade-native version of `PhysProofBridgeWCostGuards`.

module For {ℓI ℓW ℓ ℓQ : Level}
           (Input : Set ℓI)
           (size  : Input → ℕ)
           (Pℕ    : PolyPred)
           (Q     : QAdapter ℓQ)
           (gradeBound : ℕ → QAdapter.Scale Q)
           where

  open QAdapter Q renaming (Scale to Grade; _≤s_ to _≤g_)

  module C = PCWCG.For {ℓI = ℓI} {ℓW = ℓW} {ℓ = ℓ} {ℓQ = ℓQ} Input size Pℕ Q gradeBound

  Language = C.Language

  -- Helper projection to the underlying PhysDecider record.
  PD₀ : ∀ {L} → C.PhysDeciderCostGuards L → C.Base.PhysDecider L
  PD₀ pd = C.PhysDeciderCostGuards.PD pd

  record MergeMeasure (L : Language) : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
    field
      merges : C.PhysDeciderCostGuards L → Input → ℕ
      merges≤cost : ∀ (PD : C.PhysDeciderCostGuards L) (x : Input) →
                      _≤g_ (gradeBound (merges PD x)) (C.Base.PhysDecider.cost (PD₀ PD) x)

  record ProofLowerBound (L : Language) (MM : MergeMeasure L)
    : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
    field
      superPolyMerges : ∀ (PD : C.PhysDeciderCostGuards L) →
        Σ Input (λ x → ¬ (_≤g_ (gradeBound (MergeMeasure.merges MM PD x))
                            (gradeBound (C.Base.PhysDecider.bound (PD₀ PD) (size x)))))

  SuperPolyCostDet : Language → Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ)))
  SuperPolyCostDet L =
    ∀ (PD : C.PhysDeciderCostGuards L) →
      Σ Input (λ x → ¬ (_≤g_ (C.Base.PhysDecider.cost (PD₀ PD) x)
                          (gradeBound (C.Base.PhysDecider.bound (PD₀ PD) (size x)))))

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

  open PBW.Kernel K Input Size DetRun VerRun VerRunWith IsPoly gradeBound WSize public

-- Grade-native kernel bridge (TruthRoute_Grade_Only-based).

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

  open PBW.KernelG K Input Size DetRun VerRun VerRunWith PGG Pℕ WSize public
