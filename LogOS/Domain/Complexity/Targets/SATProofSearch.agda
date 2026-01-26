{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.Targets.SATProofSearch where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_; _↔_; ↔-refl)

open import LogOS.Prelude.Nat using (ℕ)
open import LogOS.Prelude.NatOrder using (≤ℕ-refl)

open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Domain.Complexity.Poly using (PolyPred)
import LogOS.Syntax.ProofSystem as PS
import LogOS.Domain.Complexity.Targets.SAT as SAT
import LogOS.Domain.Complexity.Targets.ProofSearchGraded as PSG

-- SAT as a proof-search predicate: proofs are assignments, checking is evaluation.

SATProofSystem : PS.ProofSystem SAT.CNF SAT.SAT
SATProofSystem =
  record
    { Proof    = λ _ → SAT.Assignment
    ; Check    = SAT.Check
    ; decCheck = SAT.decCheck
    ; sound    = λ φ ρ ok → ρ , ok
    }

SATProofSearch : SAT.CNF → Set
SATProofSearch = PS.Prov SATProofSystem

sat↔proofSearch : ∀ φ → SAT.SAT φ ↔ SATProofSearch φ
sat↔proofSearch _ = ↔-refl

-- Proof-complexity surface for SAT (graded, cost-aware).

module Graded
  {ℓQ : Level}
  (Pℕ : PolyPred)
  (Q  : QAdapter ℓQ)
  (gradeBound : ℕ → QAdapter.Scale Q)
  where

  module G = PSG.For {ℓI = lzero} {ℓ = lzero} {ℓQ = ℓQ} SAT.CNF SAT.cnfSize Pℕ Q gradeBound

  SATProofSystemG : G.ProofSystem SAT.SAT
  SATProofSystemG =
    record
      { core = SATProofSystem
      ; psize = λ {φ} _ → SAT.cnfSize φ
      ; polyBound = λ n → n
      ; checkCost = λ φ _ → gradeBound (SAT.cnfSize φ)
      ; checkBound = λ n → n
      ; polyCheck = PolyPred.id-isPoly Pℕ
      ; checkCost≤ = λ _ _ → QAdapter.≤s-refl Q
      ; wsize≤checkCost = λ _ _ → QAdapter.≤s-refl Q
      }

  SATThm : G.Language
  SATThm = G.Thm SATProofSystemG

  sat↔thm : ∀ φ → SAT.SAT φ ↔ SATThm φ
  sat↔thm φ =
    record
      { to = λ (ρ , ok) → ρ , (≤ℕ-refl , ok)
      ; from = λ (ρ , (_ , ok)) → ρ , ok
      }

  separationFromProofLowerBound
    : (MM : G.B.MergeMeasure SATThm)
      → G.B.ProofLowerBound SATThm MM
      → G.C.PhysNPw SATThm × ¬ G.C.PhysP SATThm
  separationFromProofLowerBound = G.thm-separates SATProofSystemG
