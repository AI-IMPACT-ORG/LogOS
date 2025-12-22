{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.TruthRoute_Grade_Only where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_; _↔_)

open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; snd)
open import Data.Sum using (_⊎_)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Kernel.Graded
import LogOS.Domain.Complexity.PolyGrade as PG

-- Kernel-native truth route (grade-only):
-- “within bound” is defined by graded Flow on boundary constraints.

module For
  {ℓ ℓI : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (Input₀ : Set ℓI)
  (Size₀  : Input₀ → ℕ)
  (DetRun₀ : Input₀ → GradedKernel.Code K)
  (VerRun₀ : Input₀ → GradedKernel.Code K)
  (VerRunWith₀ : Input₀ → GradedKernel.Code K → GradedKernel.Code K)
  where

  open GradedKernel K
  open QAdapter Q renaming (_≤s_ to _≤g_)

  private
    CP∂ : ConPoset ℓ
    CP∂ = BulkBoundary.bnd BB
    module CP∂ = ConPoset CP∂

  Input : Set ℓI
  Input = Input₀

  Size : Input → ℕ
  Size = Size₀

  DetRun : Input → GradedKernel.Code K
  DetRun = DetRun₀

  VerRun : Input → GradedKernel.Code K
  VerRun = VerRun₀

  VerRunWith : Input → GradedKernel.Code K → GradedKernel.Code K
  VerRunWith = VerRunWith₀

  Con : Set ℓ
  Con = CP∂.Con

  -- Exported kernel decode (used by bridge modules).
  decodeK : GradedKernel.Code K → Con
  decodeK = GradedKernel.decode K

  Grade : Set ℓ
  Grade = QAdapter.Scale Q

  Flow : Grade → Con → Con
  Flow = GradedClosure.Flow GTruth

  -- “Acceptance” predicates are carried on boundary constraints.
  -- (Optional) monotonicity w.r.t. the boundary order.
  AccMono : ∀ {ℓA} (Acc : Con → Set ℓA) → Set (ℓ ⊔ ℓA)
  AccMono Acc = ∀ {c d} → CP∂._⊑_ c d → Acc c → Acc d

  Flow-mono-grade : ∀ {g g'} → _≤g_ g g' → ∀ c → CP∂._⊑_ (Flow g c) (Flow g' c)
  Flow-mono-grade le c = GradedClosure.mono-grade GTruth le c

  -- Grade-indexed “within bound”.
  DetWithinAt : ∀ {ℓA} (Acc : Con → Set ℓA) → Grade → Input → Set ℓA
  DetWithinAt Acc g x = Acc (Flow g (decode (DetRun x)))

  VerWithinAt : ∀ {ℓA} (Acc : Con → Set ℓA) → Grade → Input → Set ℓA
  VerWithinAt Acc g x = Acc (Flow g (decode (VerRun x)))

  VerWithinWithAt : ∀ {ℓA} (Acc : Con → Set ℓA) → Grade → Input → GradedKernel.Code K → Set ℓA
  VerWithinWithAt Acc g x w = Acc (Flow g (decode (VerRunWith x w)))

  DetWithinAt-mono
    : ∀ {ℓA} {Acc : Con → Set ℓA}
      → AccMono Acc
      → ∀ {g g'} → _≤g_ g g' → ∀ x → DetWithinAt Acc g x → DetWithinAt Acc g' x
  DetWithinAt-mono mono g≤g' x acc =
    mono (Flow-mono-grade g≤g' (decode (DetRun x))) acc

  VerWithinAt-mono
    : ∀ {ℓA} {Acc : Con → Set ℓA}
      → AccMono Acc
      → ∀ {g g'} → _≤g_ g g' → ∀ x → VerWithinAt Acc g x → VerWithinAt Acc g' x
  VerWithinAt-mono mono g≤g' x acc =
    mono (Flow-mono-grade g≤g' (decode (VerRun x))) acc

  VerWithinWithAt-mono
    : ∀ {ℓA} {Acc : Con → Set ℓA}
      → AccMono Acc
      → ∀ {g g'} → _≤g_ g g' → ∀ x w → VerWithinWithAt Acc g x w → VerWithinWithAt Acc g' x w
  VerWithinWithAt-mono mono g≤g' x w acc =
    mono (Flow-mono-grade g≤g' (decode (VerRunWith x w))) acc

  -- Language-relative interface with correctness carried explicitly.
  Language : (ℓL : Level) → Set (ℓI ⊔ lsuc (ℓ ⊔ ℓL))
  Language ℓL = Input → Set (ℓ ⊔ ℓL)

  -- Grade-native polynomial bounds: avoid `gradeBound` in the core statements.
  module GradeBounded (PG : PG.PolyPredG Grade) where
    open PG.PolyPredG PG renaming (isPolyG to IsPolyG)

    DetPolyTimeBoundedG : ∀ {ℓA} (Acc : Con → Set ℓA) → Set (ℓ ⊔ ℓI ⊔ ℓA)
    DetPolyTimeBoundedG Acc =
      Σ (ℕ → Grade) (λ g →
        IsPolyG g
        × (∀ x → DetWithinAt Acc (g (Size x)) x))

    PolyWitnessedTotalVerificationG : ∀ {ℓA} (Acc : Con → Set ℓA) → Set (ℓ ⊔ ℓI ⊔ ℓA)
    PolyWitnessedTotalVerificationG Acc =
      Σ (ℕ → Grade) (λ g →
        IsPolyG g
        × (∀ x → Σ (GradedKernel.Code K) (λ w →
              VerWithinWithAt Acc (g (Size x)) x w)))

    -- Super-polynomial hardness of determinism for this Acc predicate.
    SuperPolyHardnessG : ∀ {ℓA} (Acc : Con → Set ℓA) → Set (ℓ ⊔ ℓI ⊔ ℓA)
    SuperPolyHardnessG Acc =
      ∀ (g : ℕ → Grade) → IsPolyG g →
        Σ Input (λ x → ¬ (DetWithinAt Acc (g (Size x)) x))

    record SpectralSeparationAssumptionsG {ℓA} (Acc : Con → Set ℓA)
      : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓA))) where
      field
        NP-witnessG   : PolyWitnessedTotalVerificationG Acc
        Det-superpolyG : SuperPolyHardnessG Acc

    record PvsNPClaimG {ℓA} (Acc : Con → Set ℓA)
      : Set (lsuc (ℓ ⊔ ℓI ⊔ ℓA)) where
      field
        NP-holdsG : PolyWitnessedTotalVerificationG Acc
        notP      : ¬ DetPolyTimeBoundedG Acc

    record PvsNPPackG {ℓA} (Acc : Con → Set ℓA) (A : SpectralSeparationAssumptionsG Acc)
      : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓA))) where
      field
        assumptions : SpectralSeparationAssumptionsG Acc
        claim       : PvsNPClaimG Acc

    noDetPolyTimeBoundedG
      : ∀ {ℓA} {Acc : Con → Set ℓA}
      → SuperPolyHardnessG Acc
      → ¬ DetPolyTimeBoundedG Acc
    noDetPolyTimeBoundedG sp (g , (polyG , within)) =
      let ex = sp g polyG in
      proj₂ ex (within (proj₁ ex))

    mkPvsNPG
      : ∀ {ℓA} {Acc : Con → Set ℓA}
      (A : SpectralSeparationAssumptionsG Acc)
      → PvsNPPackG Acc A
    mkPvsNPG {Acc = Acc} A =
      record
        { assumptions = A
        ; claim = record
            { NP-holdsG = SpectralSeparationAssumptionsG.NP-witnessG A
            ; notP      = noDetPolyTimeBoundedG {Acc = Acc}
                            (SpectralSeparationAssumptionsG.Det-superpolyG A)
            }
        }

    -- Standard pack skeleton (uniform API).
    Assumptions = SpectralSeparationAssumptionsG
    Claim       = PvsNPClaimG
    Pack        = PvsNPPackG
    mkPack      = mkPvsNPG

    record InPG {ℓL : Level} (L : Language ℓL)
      : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓL))) where
      field
        tBoundG : ℕ → Grade
        polyTG  : IsPolyG tBoundG

        Acc     : Con → Set (ℓ ⊔ ℓL)
        decAcc  : ∀ c → Acc c ⊎ ¬ (Acc c)

        correct : ∀ x →
          L x ↔ Acc (Flow (tBoundG (Size x)) (decode (DetRun x)))

    module WithWitnessSizeG {ℓW} (IsPolyW : (ℕ → ℕ) → Set ℓW)
                             (WSize₀ : GradedKernel.Code K → ℕ) where

      open import Data.NatOrder using (_≤ℕ_)

      WSize : GradedKernel.Code K → ℕ
      WSize = WSize₀

      PolyWitnessedTotalVerificationWG
        : ∀ {ℓA} (Acc : Con → Set ℓA) → Set (ℓ ⊔ ℓI ⊔ ℓA ⊔ ℓW)
      PolyWitnessedTotalVerificationWG Acc =
        Σ (ℕ → Grade) (λ g →
          IsPolyG g
          × Σ (ℕ → ℕ) (λ wBound →
              IsPolyW wBound
              × (∀ x → Σ (GradedKernel.Code K) (λ w →
                    (WSize w ≤ℕ wBound (Size x))
                    × VerWithinWithAt Acc (g (Size x)) x w))))

      record SpectralSeparationAssumptionsWG {ℓA} (Acc : Con → Set ℓA)
        : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓA ⊔ ℓW))) where
        field
          NP-witnessWG   : PolyWitnessedTotalVerificationWG Acc
          Det-superpolyG : SuperPolyHardnessG Acc

      record PvsNPClaimWG {ℓA} (Acc : Con → Set ℓA)
        : Set (lsuc (ℓ ⊔ ℓI ⊔ ℓA ⊔ ℓW)) where
        field
          NP-holdsWG : PolyWitnessedTotalVerificationWG Acc
          notP       : ¬ DetPolyTimeBoundedG Acc

      record PvsNPPackWG {ℓA} (Acc : Con → Set ℓA)
                          (A : SpectralSeparationAssumptionsWG Acc)
        : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓA ⊔ ℓW))) where
        field
          assumptions : SpectralSeparationAssumptionsWG Acc
          claim       : PvsNPClaimWG Acc

      mkPvsNPWG
        : ∀ {ℓA} {Acc : Con → Set ℓA}
        (A : SpectralSeparationAssumptionsWG Acc)
        → PvsNPPackWG Acc A
      mkPvsNPWG {Acc = Acc} A =
        record
          { assumptions = A
          ; claim = record
              { NP-holdsWG = SpectralSeparationAssumptionsWG.NP-witnessWG A
              ; notP       = noDetPolyTimeBoundedG {Acc = Acc}
                              (SpectralSeparationAssumptionsWG.Det-superpolyG A)
              }
          }

      -- Standard pack skeleton (uniform API), witness-size variant.
      AssumptionsW = SpectralSeparationAssumptionsWG
      ClaimW       = PvsNPClaimWG
      PackW        = PvsNPPackWG
      mkPackW      = mkPvsNPWG

      record InNPG {ℓL : Level} (L : Language ℓL)
        : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓL ⊔ ℓW))) where
        field
          wBound  : ℕ → ℕ
          tBoundG : ℕ → Grade
          polyW   : IsPolyW wBound
          polyTG  : IsPolyG tBoundG

          Acc     : Con → Set (ℓ ⊔ ℓL)
          decAcc  : ∀ c → Acc c ⊎ ¬ (Acc c)

          correct : ∀ x →
            L x ↔
            Σ (GradedKernel.Code K) (λ w →
              (WSize w ≤ℕ wBound (Size x))
              × Acc (Flow (tBoundG (Size x)) (decode (VerRunWith x w))))
