{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
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
import LogOS.Theorems.Meta.QuartetCore as Quartet

-- Cost-guard physical separation pipeline (grade-native):
-- PhysNPwCostGuards + proof lower bound ⇒ PhysNPwCostGuards × ¬ PhysPCostGuards.

-- Shared quartet scaffolding (used by both `Kernel` and `KernelG` routes).
module Scaffold
  {ℓCon ℓNP ℓP ℓMM : Level}
  (Con : Set ℓCon)
  (PhysNPwCostGuards : ∀ {ℓA} (Acc : Con → Set ℓA) → Set (ℓNP ⊔ ℓA))
  (PhysPCostGuards   : ∀ {ℓA} (Acc : Con → Set ℓA) → Set (ℓP ⊔ ℓA))
  (MergeMeasure      : ∀ {ℓA} (Acc : Con → Set ℓA) → Set (lsuc (lsuc (ℓMM ⊔ ℓA))))
  (ProofLowerBound
    : ∀ {ℓA} (Acc : Con → Set ℓA)
      → MergeMeasure Acc
      → Set (lsuc (lsuc (ℓMM ⊔ ℓA))))
  (mkNotP
    : ∀ {ℓA} {Acc : Con → Set ℓA}
      → (MM : MergeMeasure Acc)
      → ProofLowerBound Acc MM
      → ¬ PhysPCostGuards Acc)
  where

  record Assumptions {ℓA} (Acc : Con → Set ℓA)
    : Set (lsuc (lsuc (ℓNP ⊔ ℓP ⊔ ℓMM ⊔ ℓA))) where
    field
      inNPwCostGuards : PhysNPwCostGuards Acc
      MM     : MergeMeasure Acc
      PLB    : ProofLowerBound Acc MM

  record Claim {ℓA} (Acc : Con → Set ℓA)
    : Set (lsuc (lsuc (ℓNP ⊔ ℓP ⊔ ℓMM ⊔ ℓA))) where
    field
      NP-holds : PhysNPwCostGuards Acc
      notP     : ¬ PhysPCostGuards Acc

  module Q {ℓA} {Acc : Con → Set ℓA} =
    Quartet.Make (Assumptions Acc) (λ _ → Claim Acc)
  open Q public using (Pack; assumptionsOf; claimOf)

  mkPack : ∀ {ℓA} {Acc : Con → Set ℓA} → (A : Assumptions Acc) → Pack {ℓA} {Acc}
  mkPack {Acc = Acc} A =
    Q.mkPack
      (λ A →
        record
          { NP-holds = Assumptions.inNPwCostGuards A
          ; notP     = mkNotP {Acc = Acc} (Assumptions.MM A) (Assumptions.PLB A)
          })
      A

module For {ℓI ℓW ℓ ℓQ : Level}
           (Input : Set ℓI)
           (size  : Input → ℕ)
           (Pℕ    : PolyPred)
           (Q     : QAdapter ℓQ)
           (gradeBound : ℕ → QAdapter.Scale Q)
           where

  module C = PCWCG.For {ℓI = ℓI} {ℓW = ℓW} {ℓ = ℓ} {ℓQ = ℓQ} Input size Pℕ Q gradeBound
  module B = PBWCG.For {ℓI = ℓI} {ℓW = ℓW} {ℓ = ℓ} {ℓQ = ℓQ} Input size Pℕ Q gradeBound

  record Assumptions (L : C.Language) : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓW ⊔ ℓQ))) where
    field
      inNPwCostGuards : C.PhysNPwCostGuards L
      MM     : B.MergeMeasure L
      PLB    : B.ProofLowerBound L MM

  record Claim (L : C.Language) : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓW ⊔ ℓQ))) where
    field
      NP-holds : C.PhysNPwCostGuards L
      notP     : ¬ C.PhysPCostGuards L

  notPhysPCostGuards : ∀ {L} → B.SuperPolyCostDet L → ¬ (C.PhysPCostGuards L)
  notPhysPCostGuards {L = L} sp (pd , _) =
    let ex = sp pd in
    proj₂ ex (C.Base.PhysDecider.cost≤ (B.PD₀ pd) (proj₁ ex))

  module Q {L : C.Language} = Quartet.Make (Assumptions L) (λ _ → Claim L)
  open Q public using (Pack; assumptionsOf; claimOf)

  mkPack : ∀ {L} → (A : Assumptions L) → Pack {L}
  mkPack A =
    Q.mkPack
      (λ A →
        record
          { NP-holds = Assumptions.inNPwCostGuards A
          ; notP     = notPhysPCostGuards
                        (B.superPolyCostFromProof (Assumptions.MM A)
                                                  (Assumptions.PLB A))
          })
      A

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

  mkNotP
    : ∀ {ℓA} {Acc : C.Con → Set ℓA}
      → (MM : B.MergeMeasure Acc)
      → B.ProofLowerBound Acc MM
      → ¬ C.PhysPCostGuards Acc
  mkNotP {Acc = Acc} MM PLB =
    C.notPhysPCostGuards {Acc = Acc} (B.superPolyHardnessFromProof {Acc = Acc} MM PLB)

  module S =
    Scaffold {ℓCon = ℓ} {ℓNP = ℓ ⊔ ℓI ⊔ ℓP} {ℓP = ℓI ⊔ ℓP} {ℓMM = ℓ ⊔ ℓI ⊔ ℓP}
      C.Con C.PhysNPwCostGuards C.PhysPCostGuards
      B.MergeMeasure B.ProofLowerBound mkNotP
  open S public

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

  mkNotP
    : ∀ {ℓA} {Acc : C.Con → Set ℓA}
      → (MM : B.MergeMeasure Acc)
      → B.ProofLowerBound Acc MM
      → ¬ C.PhysPCostGuards Acc
  mkNotP {Acc = Acc} MM PLB =
    C.notPhysPCostGuards {Acc = Acc} (B.superPolyHardnessFromProof {Acc = Acc} MM PLB)

  module S =
    Scaffold {ℓCon = ℓ} {ℓNP = ℓ ⊔ ℓI} {ℓP = ℓ ⊔ ℓI} {ℓMM = ℓ ⊔ ℓI}
      C.Con C.PhysNPwCostGuards C.PhysPCostGuards
      B.MergeMeasure B.ProofLowerBound mkNotP
  open S public
