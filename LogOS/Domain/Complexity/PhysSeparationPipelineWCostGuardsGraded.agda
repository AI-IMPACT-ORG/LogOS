{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.PhysSeparationPipelineWCostGuardsGraded where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Kernel.Graded
open import LogOS.Domain.Complexity.Poly using (PolyPred)
import LogOS.Domain.Complexity.PhysicsClassesWCostGuardsGraded as PCWCG
import LogOS.Domain.Complexity.PhysProofBridgeWCostGuardsGraded as PBWCG
import LogOS.Domain.Complexity.PolyGrade as PG

-- Cost-guard physical separation pipeline (grade-native):
-- PhysNPwCostGuards + proof lower bound ⇒ PhysNPwCostGuards × ¬ PhysPCostGuards.

module For {ℓI ℓW ℓ ℓQ : Level}
           (Input : Set ℓI)
           (size  : Input → ℕ)
           (Pℕ    : PolyPred)
           (Q     : QAdapter ℓQ)
           (gradeBound : ℕ → QAdapter.Scale Q)
           (trans≤ : ∀ {a b c} → QAdapter._≤s_ Q a b → QAdapter._≤s_ Q b c → QAdapter._≤s_ Q a c)
           where

  module C = PCWCG.For {ℓI = ℓI} {ℓW = ℓW} {ℓ = ℓ} {ℓQ = ℓQ} Input size Pℕ Q gradeBound
  module B = PBWCG.For {ℓI = ℓI} {ℓW = ℓW} {ℓ = ℓ} {ℓQ = ℓQ} Input size Pℕ Q gradeBound trans≤

  record Assumptions (L : C.Language) : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓW ⊔ ℓQ))) where
    field
      inNPwCostGuards : C.PhysNPwCostGuards L
      MM     : B.MergeMeasure L
      PLB    : B.ProofLowerBound L MM

  record Claim (L : C.Language) : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓW ⊔ ℓQ))) where
    field
      NP-holds : C.PhysNPwCostGuards L
      notP     : ¬ C.PhysPCostGuards L

  record Pack (L : C.Language) (A : Assumptions L)
    : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓW ⊔ ℓQ))) where
    field
      assumptions : Assumptions L
      claim       : Claim L

  notPhysPCostGuards : ∀ {L} → B.SuperPolyCostDet L → ¬ (C.PhysPCostGuards L)
  notPhysPCostGuards {L = L} sp (pd , _) =
    let ex = sp pd in
    proj₂ ex (C.Base.PhysDecider.cost≤ (B.PD₀ pd) (proj₁ ex))

  mkPack : ∀ {L} → (A : Assumptions L) → Pack L A
  mkPack {L} A =
    record
      { assumptions = A
      ; claim =
          record
            { NP-holds = Assumptions.inNPwCostGuards A
            ; notP     = notPhysPCostGuards (B.superPolyCostFromProof (Assumptions.MM A)
                                                                     (Assumptions.PLB A))
            }
      }

-- Kernel-native separation pipeline (TruthRoute-based).

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

  module C = PCWCG.Kernel K Input Size DetRun VerRun VerRunWith IsPoly gradeBound WSize
  module B = PBWCG.Kernel K Input Size DetRun VerRun VerRunWith IsPoly gradeBound WSize

  record Assumptions {ℓA} (Acc : C.Con → Set ℓA)
    : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓP ⊔ ℓA))) where
    field
      inNPwCostGuards : C.PhysNPwCostGuards Acc
      MM     : B.MergeMeasure Acc
      PLB    : B.ProofLowerBound Acc MM

  record Claim {ℓA} (Acc : C.Con → Set ℓA)
    : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓP ⊔ ℓA))) where
    field
      NP-holds : C.PhysNPwCostGuards Acc
      notP     : ¬ C.PhysPCostGuards Acc

  record Pack {ℓA} (Acc : C.Con → Set ℓA) (A : Assumptions Acc)
    : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓP ⊔ ℓA))) where
    field
      assumptions : Assumptions Acc
      claim       : Claim Acc

  mkPack : ∀ {ℓA} {Acc : C.Con → Set ℓA} → (A : Assumptions Acc) → Pack Acc A
  mkPack {Acc = Acc} A =
    record
      { assumptions = A
      ; claim =
          record
            { NP-holds = Assumptions.inNPwCostGuards A
            ; notP     = C.notPhysPCostGuards {Acc = Acc}
                          (B.superPolyHardnessFromProof {Acc = Acc}
                             (Assumptions.MM A) (Assumptions.PLB A))
            }
      }

-- Grade-native kernel route (TruthRoute_Grade_Only-based).

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

  module C = PCWCG.KernelG K Input Size DetRun VerRun VerRunWith PGG Pℕ WSize
  module B = PBWCG.KernelG K Input Size DetRun VerRun VerRunWith PGG Pℕ WSize

  record Assumptions {ℓA} (Acc : C.Con → Set ℓA)
    : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓA))) where
    field
      inNPwCostGuards : C.PhysNPwCostGuards Acc
      MM     : B.MergeMeasure Acc
      PLB    : B.ProofLowerBound Acc MM

  record Claim {ℓA} (Acc : C.Con → Set ℓA)
    : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓA))) where
    field
      NP-holds : C.PhysNPwCostGuards Acc
      notP     : ¬ C.PhysPCostGuards Acc

  record Pack {ℓA} (Acc : C.Con → Set ℓA) (A : Assumptions Acc)
    : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓA))) where
    field
      assumptions : Assumptions Acc
      claim       : Claim Acc

  mkPack : ∀ {ℓA} {Acc : C.Con → Set ℓA} → (A : Assumptions Acc) → Pack Acc A
  mkPack {Acc = Acc} A =
    record
      { assumptions = A
      ; claim =
          record
            { NP-holds = Assumptions.inNPwCostGuards A
            ; notP     = C.notPhysPCostGuards {Acc = Acc}
                          (B.superPolyHardnessFromProof {Acc = Acc}
                             (Assumptions.MM A) (Assumptions.PLB A))
            }
      }
