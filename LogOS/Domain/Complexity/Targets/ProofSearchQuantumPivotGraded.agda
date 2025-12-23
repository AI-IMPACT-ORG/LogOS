{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.Targets.ProofSearchQuantumPivotGraded where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_)

open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Domain.Complexity.Poly using (PolyPred)
import LogOS.Domain.Complexity.Targets.ProofSearchGraded as PS
import LogOS.Domain.Complexity.ResourceSchemaGraded as QTB
import LogOS.Domain.Complexity.ObservabilityBudgetGraded as OB

-- Route B semantic pivot for proof search (grade-native):
-- swap the missing premise from merge-count lower bounds to throughput+capacity
-- bounds for non-unitary classicalization events (measurement/forgetting).

module For {ℓI ℓ ℓQ : Level}
           (Input : Set ℓI)
           (size  : Input → ℕ)
           (Pℕ    : PolyPred)
           (Q     : QAdapter ℓQ)
           (gradeBound : ℕ → QAdapter.Scale Q)
           where

  module L = PS.For {ℓI = ℓI} {ℓ = ℓ} {ℓQ = ℓQ} Input size Pℕ Q gradeBound
  module Q = QTB.For {ℓI = ℓI} {ℓ = ℓ} {ℓQ = ℓQ} Input size Pℕ Q gradeBound
  module O = OB.For {ℓI = ℓI} {ℓ = ℓ} {ℓQ = ℓQ} Input size Pℕ Q gradeBound

  Thm = L.Thm

  ClaimP : ∀ {P} (Sys : L.ProofSystem P) → Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ)))
  ClaimP Sys = ¬ (Σ (Q.QTimeDecider (Thm Sys)) (λ _ → ⊤ {ℓ = lzero}))

  ClaimPG : ∀ {P} (Sys : L.ProofSystem P) → Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ)))
  ClaimPG Sys = ¬ (Σ (Q.QTimeDeciderG (Thm Sys)) (λ _ → ⊤ {ℓ = lzero}))

  module Base where
    record Assumptions {P : Input → Set ℓ} (Sys : L.ProofSystem P)
      : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
      field
        TH : Q.Throughput
        CP : Q.Capacity
        hard : Q.Hard (Thm Sys) TH CP

    Claim : ∀ {P} (Sys : L.ProofSystem P) → Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ)))
    Claim = ClaimP

    record Pack {P : Input → Set ℓ} (Sys : L.ProofSystem P) (A : Assumptions Sys)
      : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
      field
        assumptions : Assumptions Sys
        claim       : Claim Sys

    mkPack
      : ∀ {P} {Sys : L.ProofSystem P}
        → (A : Assumptions Sys)
        → Pack Sys A
    mkPack {Sys = Sys} A =
      record
        { assumptions = A
        ; claim = Q.notPolyTime (Assumptions.TH A)
                                (Assumptions.CP A)
                                (Assumptions.hard A)
        }

  module G where
    record Assumptions {P : Input → Set ℓ} (Sys : L.ProofSystem P)
      : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
      field
        TH : Q.ThroughputG
        CP : Q.CapacityG
        hard : Q.HardG (Thm Sys) TH CP

    Claim : ∀ {P} (Sys : L.ProofSystem P) → Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ)))
    Claim = ClaimPG

    record Pack {P : Input → Set ℓ} (Sys : L.ProofSystem P) (A : Assumptions Sys)
      : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
      field
        assumptions : Assumptions Sys
        claim       : Claim Sys

    mkPack
      : ∀ {P} {Sys : L.ProofSystem P}
        → (A : Assumptions Sys)
        → Pack Sys A
    mkPack {Sys = Sys} A =
      record
        { assumptions = A
        ; claim = Q.notTimeBoundedG (Assumptions.TH A)
                                    (Assumptions.CP A)
                                    (Assumptions.hard A)
        }

  module LOB where
    record Assumptions {P : Input → Set ℓ} (Sys : L.ProofSystem P)
      : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
      field
        lob  : O.LOB
        hard : Q.Hard (Thm Sys) (O.toThroughput lob) (O.toCapacity lob)

    Claim : ∀ {P} (Sys : L.ProofSystem P) → Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ)))
    Claim = ClaimP

    record Pack {P : Input → Set ℓ} (Sys : L.ProofSystem P) (A : Assumptions Sys)
      : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
      field
        assumptions : Assumptions Sys
        claim       : Claim Sys

    mkPack
      : ∀ {P} {Sys : L.ProofSystem P}
        → (A : Assumptions Sys)
        → Pack Sys A
    mkPack {Sys = Sys} A =
      record
        { assumptions = A
        ; claim = Q.notPolyTime (O.toThroughput (Assumptions.lob A))
                                (O.toCapacity (Assumptions.lob A))
                                (Assumptions.hard A)
        }

  module LOBG where
    record Assumptions {P : Input → Set ℓ} (Sys : L.ProofSystem P)
      : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
      field
        lob  : O.LOBG
        hard : Q.HardG (Thm Sys) (O.toThroughputG lob) (O.toCapacityG lob)

    Claim : ∀ {P} (Sys : L.ProofSystem P) → Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ)))
    Claim = ClaimPG

    record Pack {P : Input → Set ℓ} (Sys : L.ProofSystem P) (A : Assumptions Sys)
      : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
      field
        assumptions : Assumptions Sys
        claim       : Claim Sys

    mkPack
      : ∀ {P} {Sys : L.ProofSystem P}
        → (A : Assumptions Sys)
        → Pack Sys A
    mkPack {Sys = Sys} A =
      record
        { assumptions = A
        ; claim = Q.notTimeBoundedG (O.toThroughputG (Assumptions.lob A))
                                    (O.toCapacityG (Assumptions.lob A))
                                    (Assumptions.hard A)
        }
