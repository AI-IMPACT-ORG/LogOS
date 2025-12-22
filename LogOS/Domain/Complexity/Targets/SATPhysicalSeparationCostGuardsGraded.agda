{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.Targets.SATPhysicalSeparationCostGuardsGraded where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.NatOrder using (_≤ℕ_; ≤ℕ-refl)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Kernel.Graded
open import LogOS.Domain.Complexity.Poly using (PolyPred)
import LogOS.Domain.Complexity.PhysicsClassesWCostGuardsGraded as PCWCG
import LogOS.Domain.Complexity.PhysProofBridgeWCostGuardsGraded as PBWCG
import LogOS.Domain.Complexity.PhysSeparationPipelineWCostGuardsGraded as Pipe
open import LogOS.Domain.Complexity.Targets.SAT as SAT

-- SAT separation statement (cost-guard, grade-native).

module For {ℓQ : Level}
           (Pℕ : PolyPred)
           (Q  : QAdapter ℓQ)
           (gradeBound : ℕ → QAdapter.Scale Q)
           (monoGradeBound : ∀ {m n} → m ≤ℕ n → QAdapter._≤s_ Q (gradeBound m) (gradeBound n))
           (trans≤ : ∀ {a b c} → QAdapter._≤s_ Q a b → QAdapter._≤s_ Q b c → QAdapter._≤s_ Q a c)
           where

  module C = PCWCG.For {ℓI = lzero} {ℓW = lzero} {ℓ = lzero} {ℓQ = ℓQ} SAT.CNF SAT.cnfSize Pℕ Q gradeBound
  module B = PBWCG.For {ℓI = lzero} {ℓW = lzero} {ℓ = lzero} {ℓQ = ℓQ} SAT.CNF SAT.cnfSize Pℕ Q gradeBound trans≤
  module P = Pipe.For {ℓI = lzero} {ℓW = lzero} {ℓ = lzero} {ℓQ = ℓQ} SAT.CNF SAT.cnfSize Pℕ Q gradeBound trans≤

  SATL : C.Language
  SATL = SAT.SAT

  inPhysNPwCostGuards-SAT : C.PhysNPwCostGuards SATL
  inPhysNPwCostGuards-SAT =
    ( record
        { PW =
            record
              { WS        = SAT.WS-SAT
              ; checkCost = λ φ _ → gradeBound (SAT.cnfSize φ)
              ; checkBound = λ n → n
              ; polyCheck = PolyPred.id-isPoly Pℕ
              ; checkCost≤ = λ _ _ → monoGradeBound ≤ℕ-refl
              }
        ; wsize≤checkCost = λ _ _ → monoGradeBound ≤ℕ-refl
        }
    , tt
    )

  separationFromProof
    : (MM : B.MergeMeasure SATL)
    → B.ProofLowerBound SATL MM
    → P.Claim SATL
  separationFromProof MM PLB =
    P.Pack.claim
      (P.mkPack (record { inNPwCostGuards = inPhysNPwCostGuards-SAT ; MM = MM ; PLB = PLB }))

-- Kernel-native SAT separation (TruthRoute-based).
-- This is parameterized by a kernel/run and an explicit SAT witness pack.

module Kernel
  {ℓ ℓP ℓA : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (DetRun : SAT.CNF → GradedKernel.Code K)
  (VerRun : SAT.CNF → GradedKernel.Code K)
  (VerRunWith : SAT.CNF → GradedKernel.Code K → GradedKernel.Code K)
  (IsPoly : (ℕ → ℕ) → Set ℓP)
  (gradeBound : ℕ → QAdapter.Scale Q)
  (WSize : GradedKernel.Code K → ℕ)
  where

  module C = PCWCG.Kernel K SAT.CNF SAT.cnfSize DetRun VerRun VerRunWith IsPoly gradeBound WSize
  module B = PBWCG.Kernel K SAT.CNF SAT.cnfSize DetRun VerRun VerRunWith IsPoly gradeBound WSize
  module P = Pipe.Kernel K SAT.CNF SAT.cnfSize DetRun VerRun VerRunWith IsPoly gradeBound WSize

  separationFromProof
    : {Acc : C.Con → Set ℓA}
      → C.PhysNPwCostGuards Acc
      → (MM : B.MergeMeasure Acc)
      → B.ProofLowerBound Acc MM
      → P.Claim Acc
  separationFromProof inNPwCostGuards MM PLB =
    P.Pack.claim
      (P.mkPack (record { inNPwCostGuards = inNPwCostGuards ; MM = MM ; PLB = PLB }))
