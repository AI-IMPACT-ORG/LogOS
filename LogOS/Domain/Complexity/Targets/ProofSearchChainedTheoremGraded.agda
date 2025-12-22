{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.Targets.ProofSearchChainedTheoremGraded where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import Data.Product using (Σ; _,_)

open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Domain.Complexity.Poly using (PolyPred)
import LogOS.Domain.Complexity.ProofSearchBoundary as B
import LogOS.Domain.Complexity.ProofSearchCapstoneGraded as Cap
import LogOS.Domain.Complexity.ResourceSchemaGraded as RS
import LogOS.Domain.Complexity.ObservabilityBudgetGraded as OB

-- One chained theorem (grade-native entrypoint) for the “verification vs search” story.

module For {ℓI ℓ ℓQ : Level}
           (Input : Set ℓI)
           (size  : Input → ℕ)
           (Pℕ    : PolyPred)
           (P     : Input → Set ℓ)
           (Q     : QAdapter ℓQ)
           (gradeBound : ℕ → QAdapter.Scale Q)
           where

  module PB = B.For {ℓI = ℓI} {ℓ = ℓ} Input P
  module R  = RS.For {ℓI = ℓI} {ℓ = ℓ} {ℓQ = ℓQ} Input size Pℕ Q gradeBound
  module C  = Cap.For {ℓI = ℓI} {ℓ = ℓ} {ℓQ = ℓQ} Input size Pℕ P Q gradeBound
  module O  = OB.For {ℓI = ℓI} {ℓ = ℓ} {ℓQ = ℓQ} Input size Pℕ Q gradeBound

  ClaimP : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ)))
  ClaimP = ¬ (Σ (R.QTimeDecider P) (λ _ → ⊤ {ℓ = lzero}))

  ClaimPG : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ)))
  ClaimPG = ¬ (Σ (R.QTimeDeciderG P) (λ _ → ⊤ {ℓ = lzero}))

  module Base where
    record Assumptions (PS : PB.ProofSystem) : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
      field
        complete : PB.Complete PS
        TH   : R.Throughput
        CP   : R.Capacity
        hard : R.Hard (PB.Prov∞ PS) TH CP

    Claim : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ)))
    Claim = ClaimP

    record Pack (PS : PB.ProofSystem) (A : Assumptions PS)
      : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
      field
        assumptions : Assumptions PS
        claim       : Claim

    mkPack : ∀ {PS} → (A : Assumptions PS) → Pack PS A
    mkPack {PS} A =
      record
        { assumptions = A
        ; claim = C.notPolyTime-P (Assumptions.complete A)
                                   (Assumptions.TH A)
                                   (Assumptions.CP A)
                                   (Assumptions.hard A)
        }

  module G where
    record Assumptions (PS : PB.ProofSystem) : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
      field
        complete : PB.Complete PS
        TH   : R.ThroughputG
        CP   : R.CapacityG
        hard : R.HardG (PB.Prov∞ PS) TH CP

    Claim : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ)))
    Claim = ClaimPG

    record Pack (PS : PB.ProofSystem) (A : Assumptions PS)
      : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
      field
        assumptions : Assumptions PS
        claim       : Claim

    mkPack : ∀ {PS} → (A : Assumptions PS) → Pack PS A
    mkPack {PS} A =
      record
        { assumptions = A
        ; claim = C.notTimeBoundedG-P (Assumptions.complete A)
                                      (Assumptions.TH A)
                                      (Assumptions.CP A)
                                      (Assumptions.hard A)
        }

  module LOB where
    record Assumptions (PS : PB.ProofSystem) : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
      field
        complete : PB.Complete PS
        lob  : O.LOB
        hard : R.Hard (PB.Prov∞ PS) (O.toThroughput lob) (O.toCapacity lob)

    Claim : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ)))
    Claim = ClaimP

    record Pack (PS : PB.ProofSystem) (A : Assumptions PS)
      : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
      field
        assumptions : Assumptions PS
        claim       : Claim

    mkPack : ∀ {PS} → (A : Assumptions PS) → Pack PS A
    mkPack {PS} A =
      record
        { assumptions = A
        ; claim = C.notPolyTime-P (Assumptions.complete A)
                                   (O.toThroughput (Assumptions.lob A))
                                   (O.toCapacity (Assumptions.lob A))
                                   (Assumptions.hard A)
        }

  module LOBG where
    record Assumptions (PS : PB.ProofSystem) : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
      field
        complete : PB.Complete PS
        lob  : O.LOBG
        hard : R.HardG (PB.Prov∞ PS) (O.toThroughputG lob) (O.toCapacityG lob)

    Claim : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ)))
    Claim = ClaimPG

    record Pack (PS : PB.ProofSystem) (A : Assumptions PS)
      : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
      field
        assumptions : Assumptions PS
        claim       : Claim

    mkPack : ∀ {PS} → (A : Assumptions PS) → Pack PS A
    mkPack {PS} A =
      record
        { assumptions = A
        ; claim = C.notTimeBoundedG-P (Assumptions.complete A)
                                      (O.toThroughputG (Assumptions.lob A))
                                      (O.toCapacityG (Assumptions.lob A))
                                      (Assumptions.hard A)
        }
