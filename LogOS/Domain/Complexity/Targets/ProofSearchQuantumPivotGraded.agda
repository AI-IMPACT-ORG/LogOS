{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.Targets.ProofSearchQuantumPivotGraded where

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop using (NoWitness)

open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_)

open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Domain.Complexity.Poly using (PolyPred)
import LogOS.Domain.Complexity.Targets.ProofSearchGraded as PS
import LogOS.Domain.Complexity.ResourceSchemaGraded as QTB
import LogOS.Domain.Complexity.ObservabilityBudgetGraded as OB
import LogOS.Theorems.Meta.QuartetCore as Quartet

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
  ClaimP Sys = Prop.NoWitness (Q.QTimeDecider (Thm Sys))

  ClaimPG : ∀ {P} (Sys : L.ProofSystem P) → Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ)))
  ClaimPG Sys = Prop.NoWitness (Q.QTimeDeciderG (Thm Sys))

  module Base where
    record Assumptions {P : Input → Set ℓ} (Sys : L.ProofSystem P)
      : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
      field
        TH : Q.Throughput
        CP : Q.Capacity
        hard : Q.Hard (Thm Sys) TH CP

    Claim : ∀ {P} (Sys : L.ProofSystem P) → Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ)))
    Claim = ClaimP

    derive
      : ∀ {P} {Sys : L.ProofSystem P}
      → Assumptions Sys
      → Claim Sys
    derive A =
      Q.notPolyTime (Assumptions.TH A)
                    (Assumptions.CP A)
                    (Assumptions.hard A)

    module QPack {P : Input → Set ℓ} {Sys : L.ProofSystem P} =
      Quartet.MakeConstPack (Assumptions Sys) (Claim Sys) derive
    open QPack public using (Pack; assumptionsOf; claimOf; mkPack)

  module G where
    record Assumptions {P : Input → Set ℓ} (Sys : L.ProofSystem P)
      : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
      field
        TH : Q.ThroughputG
        CP : Q.CapacityG
        hard : Q.HardG (Thm Sys) TH CP

    Claim : ∀ {P} (Sys : L.ProofSystem P) → Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ)))
    Claim = ClaimPG

    derive
      : ∀ {P} {Sys : L.ProofSystem P}
      → Assumptions Sys
      → Claim Sys
    derive A =
      Q.notTimeBoundedG (Assumptions.TH A)
                        (Assumptions.CP A)
                        (Assumptions.hard A)

    module QPack {P : Input → Set ℓ} {Sys : L.ProofSystem P} =
      Quartet.MakeConstPack (Assumptions Sys) (Claim Sys) derive
    open QPack public using (Pack; assumptionsOf; claimOf; mkPack)

  module LOB where
    record Assumptions {P : Input → Set ℓ} (Sys : L.ProofSystem P)
      : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
      field
        lob  : O.LOB
        hard : Q.Hard (Thm Sys) (O.toThroughput lob) (O.toCapacity lob)

    Claim : ∀ {P} (Sys : L.ProofSystem P) → Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ)))
    Claim = ClaimP

    derive
      : ∀ {P} {Sys : L.ProofSystem P}
      → Assumptions Sys
      → Claim Sys
    derive A =
      Q.notPolyTime (O.toThroughput (Assumptions.lob A))
                    (O.toCapacity (Assumptions.lob A))
                    (Assumptions.hard A)

    module QPack {P : Input → Set ℓ} {Sys : L.ProofSystem P} =
      Quartet.MakeConstPack (Assumptions Sys) (Claim Sys) derive
    open QPack public using (Pack; assumptionsOf; claimOf; mkPack)

  module LOBG where
    record Assumptions {P : Input → Set ℓ} (Sys : L.ProofSystem P)
      : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
      field
        lob  : O.LOBG
        hard : Q.HardG (Thm Sys) (O.toThroughputG lob) (O.toCapacityG lob)

    Claim : ∀ {P} (Sys : L.ProofSystem P) → Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ)))
    Claim = ClaimPG

    derive
      : ∀ {P} {Sys : L.ProofSystem P}
      → Assumptions Sys
      → Claim Sys
    derive A =
      Q.notTimeBoundedG (O.toThroughputG (Assumptions.lob A))
                        (O.toCapacityG (Assumptions.lob A))
                        (Assumptions.hard A)

    module QPack {P : Input → Set ℓ} {Sys : L.ProofSystem P} =
      Quartet.MakeConstPack (Assumptions Sys) (Claim Sys) derive
    open QPack public using (Pack; assumptionsOf; claimOf; mkPack)
