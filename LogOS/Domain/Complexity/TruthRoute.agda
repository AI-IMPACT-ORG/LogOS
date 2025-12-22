{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.TruthRoute where

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
import LogOS.Domain.Complexity.TruthRoute_Grade_Only as TRG

-- Deprecated compatibility wrapper: prefers the grade-native core in TruthRoute_Grade_Only.
-- This module keeps the ℕ-bound interface for downstream alignment with the literature.

module For
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

  open GradedKernel K

  module Core = TRG.For K Input₀ Size₀ DetRun₀ VerRun₀ VerRunWith₀
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

  -- ------------------------------------------------------------------------
  -- Standard pack skeleton (uniform API).
  --
  -- `TruthRoute` is the canonical example: a pack is a bundle of assumptions
  -- plus the resulting claim. To make other storylines feel uniform, we export
  -- the standard names as aliases.

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
        L x ↔ Acc (Flow (gradeBound (tBound (Size x))) (decode (DetRun x)))

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
      t , (polyT , (λ x → let ex = wit x in proj₁ ex , Data.Product._×_.snd (proj₂ ex)))

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
            × Acc (Flow (gradeBound (tBound (Size x))) (decode (VerRunWith x w))))

  -- Grade-native polynomial bounds: core route (re-exported from TruthRoute_Grade_Only).
  module GradeBounded = Core.GradeBounded
