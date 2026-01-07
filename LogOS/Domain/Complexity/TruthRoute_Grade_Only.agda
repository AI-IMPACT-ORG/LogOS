{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.TruthRoute_Grade_Only where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_; _↔_; ⊥-elim)

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

  -- Fuel-free / budget-free variants: “within some bound”.
  --
  -- This mirrors `LogOS.Computation.Scheme`: unindexed computation is the
  -- existence of a bounded computation. Here: acceptance holds after `Flow`
  -- at some grade, for some (unspecified) resource bound.

  DetWithin : ∀ {ℓA} (Acc : Con → Set ℓA) → Input → Set (ℓ ⊔ ℓA)
  DetWithin Acc x = Σ Grade (λ g → DetWithinAt Acc g x)

  VerWithin : ∀ {ℓA} (Acc : Con → Set ℓA) → Input → Set (ℓ ⊔ ℓA)
  VerWithin Acc x = Σ Grade (λ g → VerWithinAt Acc g x)

  VerWithinWith : ∀ {ℓA} (Acc : Con → Set ℓA) → Input → Set (ℓ ⊔ ℓA)
  VerWithinWith Acc x =
    Σ Grade (λ g → Σ (GradedKernel.Code K) (λ w → VerWithinWithAt Acc g x w))

  DetWithinAt→DetWithin : ∀ {ℓA} {Acc : Con → Set ℓA} {g x} → DetWithinAt Acc g x → DetWithin Acc x
  DetWithinAt→DetWithin {g = g} acc = g , acc

  VerWithinAt→VerWithin : ∀ {ℓA} {Acc : Con → Set ℓA} {g x} → VerWithinAt Acc g x → VerWithin Acc x
  VerWithinAt→VerWithin {g = g} acc = g , acc

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

-- ℕ-bounded “within bound” via a gradeBound map.
-- This lives here (instead of a separate shim module) to keep the core
-- TruthRoute story grade-native while still supporting literature-aligned
-- ℕ-indexed bounds where needed.

module ForNat
  {ℓ ℓI ℓP : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (Input₀ : Set ℓI)
  (Size₀  : Input₀ → ℕ)
  (DetRun₀ : Input₀ → GradedKernel.Code K)
  (VerRun₀ : Input₀ → GradedKernel.Code K)
  (VerRunWith₀ : Input₀ → GradedKernel.Code K → GradedKernel.Code K)
  (IsPoly₀ : (ℕ → ℕ) → Set ℓP)
  (gradeBound₀ : ℕ → QAdapter.Scale Q)
  where

  module Core = For K Input₀ Size₀ DetRun₀ VerRun₀ VerRunWith₀
  open Core public using
    ( Input; Size; DetRun; VerRun; VerRunWith
    ; Con; decodeK; Grade; Flow
    ; AccMono; Flow-mono-grade
    ; DetWithinAt; VerWithinAt; VerWithinWithAt
    ; DetWithinAt-mono; VerWithinAt-mono; VerWithinWithAt-mono
    ; Language
    )

  IsPoly : (ℕ → ℕ) → Set ℓP
  IsPoly = IsPoly₀

  gradeBound : ℕ → QAdapter.Scale Q
  gradeBound = gradeBound₀

  -- ℕ-bounded “within bound” via gradeBound.
  DetWithin : ∀ {ℓA} (Acc : Con → Set ℓA) → ℕ → Input → Set ℓA
  DetWithin Acc t x = DetWithinAt Acc (gradeBound t) x

  VerWithin : ∀ {ℓA} (Acc : Con → Set ℓA) → ℕ → Input → Set ℓA
  VerWithin Acc t x = VerWithinAt Acc (gradeBound t) x

  VerWithinWith : ∀ {ℓA} (Acc : Con → Set ℓA) → ℕ → Input → GradedKernel.Code K → Set ℓA
  VerWithinWith Acc t x w = VerWithinWithAt Acc (gradeBound t) x w

  DetPolyTimeBounded : ∀ {ℓA} (Acc : Con → Set ℓA) → Set (ℓI ⊔ ℓP ⊔ ℓA)
  DetPolyTimeBounded Acc =
    Σ (ℕ → ℕ) (λ p →
      IsPoly p
      × (∀ x → DetWithin Acc (p (Size x)) x))

  PolyWitnessedTotalVerification : ∀ {ℓA} (Acc : Con → Set ℓA) → Set (ℓ ⊔ ℓI ⊔ ℓP ⊔ ℓA)
  PolyWitnessedTotalVerification Acc =
    Σ (ℕ → ℕ) (λ p →
      IsPoly p
      × (∀ x → Σ (GradedKernel.Code K) (λ w → VerWithinWith Acc (p (Size x)) x w)))

  -- Super-polynomial hardness of determinism for this Acc predicate.
  SuperPolyHardness : ∀ {ℓA} (Acc : Con → Set ℓA) → Set (ℓI ⊔ ℓP ⊔ ℓA)
  SuperPolyHardness Acc =
    ∀ (p : ℕ → ℕ) → IsPoly p →
      Σ Input (λ x → ¬ (DetWithin Acc (p (Size x)) x))

  record SpectralSeparationAssumptions {ℓA} (Acc : Con → Set ℓA)
    : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓP ⊔ ℓA))) where
    field
      NP-witness   : PolyWitnessedTotalVerification Acc
      Det-superpoly : SuperPolyHardness Acc

  record PvsNPClaim {ℓA} (Acc : Con → Set ℓA)
    : Set (lsuc (ℓ ⊔ ℓI ⊔ ℓP ⊔ ℓA)) where
    field
      NP-holds : PolyWitnessedTotalVerification Acc
      notP     : ¬ DetPolyTimeBounded Acc

  record PvsNPPack {ℓA} (Acc : Con → Set ℓA) (A : SpectralSeparationAssumptions Acc)
    : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓP ⊔ ℓA))) where
    field
      assumptions : SpectralSeparationAssumptions Acc
      claim       : PvsNPClaim Acc

  noDetPolyTimeBounded : ∀ {ℓA} {Acc : Con → Set ℓA} → SuperPolyHardness Acc → ¬ DetPolyTimeBounded Acc
  noDetPolyTimeBounded sp (p , (polyP , boundD)) =
    let ex = sp p polyP in
    let x  = proj₁ ex in
    let notLe = proj₂ ex in
    ⊥-elim (notLe (boundD x))

  mkPvsNP : ∀ {ℓA} {Acc : Con → Set ℓA} (A : SpectralSeparationAssumptions Acc) → PvsNPPack Acc A
  mkPvsNP {Acc = Acc} A =
    record
      { assumptions = A
      ; claim = record
          { NP-holds = SpectralSeparationAssumptions.NP-witness A
          ; notP     = noDetPolyTimeBounded {Acc = Acc} (SpectralSeparationAssumptions.Det-superpoly A)
          }
      }

  -- Standard pack skeleton (uniform API).
  Assumptions = SpectralSeparationAssumptions
  Claim       = PvsNPClaim
  Pack        = PvsNPPack
  mkPack      = mkPvsNP

  -- Language-relative interface with correctness carried explicitly.

  record InP {ℓL : Level} (L : Language ℓL) : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓL ⊔ ℓP))) where
    field
      tBound  : ℕ → ℕ
      polyT   : IsPoly tBound

      Acc     : Con → Set (ℓ ⊔ ℓL)
      decAcc  : ∀ c → Acc c ⊎ ¬ (Acc c)

      correct : ∀ x →
        L x ↔ Acc (Flow (gradeBound (tBound (Size x))) (decodeK (DetRun x)))

  -- Witness-size refinement (optional layer).

  module WithWitnessSize (WSize₀ : GradedKernel.Code K → ℕ) where

    open import Data.NatOrder using (_≤ℕ_)

    WSize : GradedKernel.Code K → ℕ
    WSize = WSize₀

    PolyWitnessedTotalVerificationW : ∀ {ℓA} (Acc : Con → Set ℓA) → Set (ℓ ⊔ ℓI ⊔ ℓP ⊔ ℓA)
    PolyWitnessedTotalVerificationW Acc =
      Σ (ℕ → ℕ) (λ t →
        IsPoly t
        × Σ (ℕ → ℕ) (λ wBound →
            IsPoly wBound
            × (∀ x → Σ (GradedKernel.Code K) (λ w →
                  (WSize w ≤ℕ wBound (Size x))
                  × VerWithinWith Acc (t (Size x)) x w))))

    -- Forget the witness-size bound.
    forgetW
      : ∀ {ℓA} {Acc : Con → Set ℓA}
      → PolyWitnessedTotalVerificationW Acc
      → PolyWitnessedTotalVerification Acc
    forgetW (t , (polyT , (wBound , (polyW , wit)))) =
      t , (polyT , (λ x → let ex = wit x in proj₁ ex , snd (proj₂ ex)))

    record SpectralSeparationAssumptionsW {ℓA} (Acc : Con → Set ℓA)
      : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓP ⊔ ℓA))) where
      field
        NP-witnessW   : PolyWitnessedTotalVerificationW Acc
        Det-superpoly : SuperPolyHardness Acc

    record PvsNPClaimW {ℓA} (Acc : Con → Set ℓA)
      : Set (lsuc (ℓ ⊔ ℓI ⊔ ℓP ⊔ ℓA)) where
      field
        NP-holdsW : PolyWitnessedTotalVerificationW Acc
        notP      : ¬ DetPolyTimeBounded Acc

    record PvsNPPackW {ℓA} (Acc : Con → Set ℓA) (A : SpectralSeparationAssumptionsW Acc)
      : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓP ⊔ ℓA))) where
      field
        assumptions : SpectralSeparationAssumptionsW Acc
        claim       : PvsNPClaimW Acc

    mkPvsNPW : ∀ {ℓA} {Acc : Con → Set ℓA} (A : SpectralSeparationAssumptionsW Acc) → PvsNPPackW Acc A
    mkPvsNPW {Acc = Acc} A =
      record
        { assumptions = A
        ; claim = record
            { NP-holdsW = SpectralSeparationAssumptionsW.NP-witnessW A
            ; notP      = noDetPolyTimeBounded {Acc = Acc} (SpectralSeparationAssumptionsW.Det-superpoly A)
            }
        }

    record InNP {ℓL : Level} (L : Language ℓL) : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓL ⊔ ℓP))) where
      field
        wBound  : ℕ → ℕ
        tBound  : ℕ → ℕ
        polyW   : IsPoly wBound
        polyT   : IsPoly tBound

        Acc     : Con → Set (ℓ ⊔ ℓL)
        decAcc  : ∀ c → Acc c ⊎ ¬ (Acc c)

        correct : ∀ x →
          L x ↔
          Σ (GradedKernel.Code K) (λ w →
            (WSize w ≤ℕ wBound (Size x))
            × Acc (Flow (gradeBound (tBound (Size x))) (decodeK (VerRunWith x w))))

  -- Grade-native polynomial bounds: core route (re-exported from `For`).
  module GradeBounded = Core.GradeBounded
