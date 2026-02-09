{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Complexity.TruthRoute_Grade_Only where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_; _↔_; ⊥-elim)

open import LogOS.Prelude using (ℕ)
open import LogOS.Prelude using (Σ; _,_; proj₁; proj₂; _×_; snd)
open import LogOS.Prelude using (_⊎_)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Adjunction using (MonoidalOps)
open import LogOS.API.Kernel.Graded
import LogOS.API.Kernel.Graded.Endo as GEndo
import LogOS.Complexity.PolyGrade as PG

-- Kernel-native truth route (grade-only):
-- “within bound” is defined by graded Flow on boundary constraints.

module Core
  {ℓ ℓI ℓW : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  where

  open GradedKernel K
  open QAdapter Q renaming (_≤s_ to _≤g_)

  private
    CP∂ : ConPreorder ℓ
    CP∂ = BulkBoundary.bnd BB
    module CP∂ = ConPreorder CP∂

  Con : Set ℓ
  Con = CP∂.Con

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

  module With
    (Input₀ : Set ℓI)
    (Size₀  : Input₀ → ℕ)
    (Witness₀ : Set ℓW)
    (DetObs₀ : Input₀ → Con)
    (VerObs₀ : Input₀ → Con)
    (VerObsWith₀ : Input₀ → Witness₀ → Con)
    where

    Input : Set ℓI
    Input = Input₀

    Size : Input → ℕ
    Size = Size₀

    Witness : Set ℓW
    Witness = Witness₀

    DetObs : Input → Con
    DetObs = DetObs₀

    VerObs : Input → Con
    VerObs = VerObs₀

    VerObsWith : Input → Witness → Con
    VerObsWith = VerObsWith₀

    -- Grade-indexed “within bound”.
    DetWithinAt : ∀ {ℓA} (Acc : Con → Set ℓA) → Grade → Input → Set ℓA
    DetWithinAt Acc g x = Acc (Flow g (DetObs x))

    VerWithinAt : ∀ {ℓA} (Acc : Con → Set ℓA) → Grade → Input → Set ℓA
    VerWithinAt Acc g x = Acc (Flow g (VerObs x))

    VerWithinWithAt : ∀ {ℓA} (Acc : Con → Set ℓA) → Grade → Input → Witness → Set ℓA
    VerWithinWithAt Acc g x w = Acc (Flow g (VerObsWith x w))

    -- Fuel-free / budget-free variants: “within some bound”.
    --
    -- This mirrors `LogOS.Computation.Scheme`: unindexed computation is the
    -- existence of a bounded computation. Here: acceptance holds after `Flow`
    -- at some grade, for some (unspecified) resource bound.

    DetWithin : ∀ {ℓA} (Acc : Con → Set ℓA) → Input → Set (ℓ ⊔ ℓA)
    DetWithin Acc x = Σ Grade (λ g → DetWithinAt Acc g x)

    VerWithin : ∀ {ℓA} (Acc : Con → Set ℓA) → Input → Set (ℓ ⊔ ℓA)
    VerWithin Acc x = Σ Grade (λ g → VerWithinAt Acc g x)

    VerWithinWith : ∀ {ℓA} (Acc : Con → Set ℓA) → Input → Set (ℓ ⊔ ℓW ⊔ ℓA)
    VerWithinWith Acc x =
      Σ Grade (λ g → Σ Witness (λ w → VerWithinWithAt Acc g x w))

    DetWithinAt→DetWithin : ∀ {ℓA} {Acc : Con → Set ℓA} {g x} → DetWithinAt Acc g x → DetWithin Acc x
    DetWithinAt→DetWithin {g = g} acc = g , acc

    VerWithinAt→VerWithin : ∀ {ℓA} {Acc : Con → Set ℓA} {g x} → VerWithinAt Acc g x → VerWithin Acc x
    VerWithinAt→VerWithin {g = g} acc = g , acc

    DetWithinAt-mono
      : ∀ {ℓA} {Acc : Con → Set ℓA}
        → AccMono Acc
        → ∀ {g g'} → _≤g_ g g' → ∀ x → DetWithinAt Acc g x → DetWithinAt Acc g' x
    DetWithinAt-mono mono g≤g' x acc =
      mono (Flow-mono-grade g≤g' (DetObs x)) acc

    VerWithinAt-mono
      : ∀ {ℓA} {Acc : Con → Set ℓA}
        → AccMono Acc
        → ∀ {g g'} → _≤g_ g g' → ∀ x → VerWithinAt Acc g x → VerWithinAt Acc g' x
    VerWithinAt-mono mono g≤g' x acc =
      mono (Flow-mono-grade g≤g' (VerObs x)) acc

    VerWithinWithAt-mono
      : ∀ {ℓA} {Acc : Con → Set ℓA}
        → AccMono Acc
        → ∀ {g g'} → _≤g_ g g' → ∀ x w → VerWithinWithAt Acc g x w → VerWithinWithAt Acc g' x w
    VerWithinWithAt-mono mono g≤g' x w acc =
      mono (Flow-mono-grade g≤g' (VerObsWith x w)) acc

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

      PolyTotalWitnessedVerificationG : ∀ {ℓA} (Acc : Con → Set ℓA) → Set (ℓ ⊔ ℓI ⊔ ℓW ⊔ ℓA)
      PolyTotalWitnessedVerificationG Acc =
        Σ (ℕ → Grade) (λ g →
          IsPolyG g
          × (∀ x → Σ Witness (λ w →
                VerWithinWithAt Acc (g (Size x)) x w)))

      -- Super-polynomial hardness of determinism for this Acc predicate.
      SuperPolyHardnessG : ∀ {ℓA} (Acc : Con → Set ℓA) → Set (ℓ ⊔ ℓI ⊔ ℓA)
      SuperPolyHardnessG Acc =
        ∀ (g : ℕ → Grade) → IsPolyG g →
          Σ Input (λ x → ¬ (DetWithinAt Acc (g (Size x)) x))

      record SpectralSeparationAssumptionsG {ℓA} (Acc : Con → Set ℓA)
        : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓW ⊔ ℓA))) where
        field
          total-witnessG : PolyTotalWitnessedVerificationG Acc
          Det-superpolyG : SuperPolyHardnessG Acc

      record PvsNPClaimG {ℓA} (Acc : Con → Set ℓA)
        : Set (lsuc (ℓ ⊔ ℓI ⊔ ℓW ⊔ ℓA)) where
        field
          total-holdsG : PolyTotalWitnessedVerificationG Acc
          notP         : ¬ DetPolyTimeBoundedG Acc

      record PvsNPPackG {ℓA} (Acc : Con → Set ℓA) (A : SpectralSeparationAssumptionsG Acc)
        : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓW ⊔ ℓA))) where
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
              { total-holdsG = SpectralSeparationAssumptionsG.total-witnessG A
              ; notP         = noDetPolyTimeBoundedG {Acc = Acc}
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
            L x ↔ Acc (Flow (tBoundG (Size x)) (DetObs x))

      module WithWitnessSizeG {ℓW'} (IsPolyW : (ℕ → ℕ) → Set ℓW')
                                 (WSize₀ : Witness → ℕ) where

        open import LogOS.Prelude.NatOrder using (_≤ℕ_)

        WSize : Witness → ℕ
        WSize = WSize₀

        PolyTotalWitnessedVerificationWG
          : ∀ {ℓA} (Acc : Con → Set ℓA) → Set (ℓ ⊔ ℓI ⊔ ℓW ⊔ ℓA ⊔ ℓW')
        PolyTotalWitnessedVerificationWG Acc =
          Σ (ℕ → Grade) (λ g →
            IsPolyG g
            × Σ (ℕ → ℕ) (λ wBound →
                IsPolyW wBound
                × (∀ x → Σ Witness (λ w →
                      (WSize w ≤ℕ wBound (Size x))
                      × VerWithinWithAt Acc (g (Size x)) x w))))

        record SpectralSeparationAssumptionsWG {ℓA} (Acc : Con → Set ℓA)
          : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓW ⊔ ℓA ⊔ ℓW'))) where
          field
            total-witnessWG : PolyTotalWitnessedVerificationWG Acc
            Det-superpolyG  : SuperPolyHardnessG Acc

        record PvsNPClaimWG {ℓA} (Acc : Con → Set ℓA)
          : Set (lsuc (ℓ ⊔ ℓI ⊔ ℓW ⊔ ℓA ⊔ ℓW')) where
          field
            total-holdsWG : PolyTotalWitnessedVerificationWG Acc
            notP          : ¬ DetPolyTimeBoundedG Acc

        record PvsNPPackWG {ℓA} (Acc : Con → Set ℓA)
                            (A : SpectralSeparationAssumptionsWG Acc)
          : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓW ⊔ ℓA ⊔ ℓW'))) where
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
                { total-holdsWG = SpectralSeparationAssumptionsWG.total-witnessWG A
                ; notP          = noDetPolyTimeBoundedG {Acc = Acc}
                                  (SpectralSeparationAssumptionsWG.Det-superpolyG A)
                }
            }

        -- Standard pack skeleton (uniform API), witness-size variant.
        AssumptionsW = SpectralSeparationAssumptionsWG
        ClaimW       = PvsNPClaimWG
        PackW        = PvsNPPackWG
        mkPackW      = mkPvsNPWG

        record InNPG {ℓL : Level} (L : Language ℓL)
          : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓL ⊔ ℓW ⊔ ℓW'))) where
          field
            wBound  : ℕ → ℕ
            tBoundG : ℕ → Grade
            polyW   : IsPolyW wBound
            polyTG  : IsPolyG tBoundG

            Acc     : Con → Set (ℓ ⊔ ℓL)
            decAcc  : ∀ c → Acc c ⊎ ¬ (Acc c)

            correct : ∀ x →
              L x ↔
              Σ Witness (λ w →
                (WSize w ≤ℕ wBound (Size x))
                × Acc (Flow (tBoundG (Size x)) (VerObsWith x w)))

module NonUniform
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

  module C = Core {ℓ = ℓ} {ℓI = ℓI} {ℓW = ℓ} K
  open C public using (Con; Grade; Flow; AccMono; Flow-mono-grade)
  open GradedKernel K

  module M = C.With Input₀ Size₀ (GradedKernel.Code K)
               (λ x → decode (DetRun₀ x))
               (λ x → decode (VerRun₀ x))
               (λ x w → decode (VerRunWith₀ x w))

  open M public

  DetRun : Input → GradedKernel.Code K
  DetRun = DetRun₀

  VerRun : Input → GradedKernel.Code K
  VerRun = VerRun₀

  VerRunWith : Input → GradedKernel.Code K → GradedKernel.Code K
  VerRunWith = VerRunWith₀

  decodeK : GradedKernel.Code K → Con
  decodeK = GradedKernel.decode K

module Uniform
  {ℓ ℓI : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (Input₀ : Set ℓI)
  (Size₀  : Input₀ → ℕ)
  (encodeI₀ : Input₀ → ConPreorder.Con (BulkBoundary.bnd (GradedKernel.BB K)))
  (encodeW₀ : GradedKernel.Code K → ConPreorder.Con (BulkBoundary.bnd (GradedKernel.BB K)))
  (DetEndo₀ : GEndo.Endo K)
  (VerEndo₀ : GEndo.Endo K)
  (VerEndoWith₀ : GEndo.Endo K)
  where

  module C = Core {ℓ = ℓ} {ℓI = ℓI} {ℓW = ℓ} K
  open C public using (Con; Grade; Flow; AccMono; Flow-mono-grade)
  open GradedKernel K
  open MonoidalOps (GradedKernel.MBnd K) using (_⊗_)

  decodeK : GradedKernel.Code K → Con
  decodeK = GradedKernel.decode K

  module M = C.With Input₀ Size₀ (GradedKernel.Code K)
               (λ x → GEndo.Endo.fn DetEndo₀ (encodeI₀ x))
               (λ x → GEndo.Endo.fn VerEndo₀ (encodeI₀ x))
               (λ x w → GEndo.Endo.fn VerEndoWith₀ (encodeI₀ x ⊗ encodeW₀ w))

  open M public

  encodeI : Input → Con
  encodeI = encodeI₀

  encodeW : GradedKernel.Code K → Con
  encodeW = encodeW₀

  DetEndo : GEndo.Endo K
  DetEndo = DetEndo₀

  VerEndo : GEndo.Endo K
  VerEndo = VerEndo₀

  VerEndoWith : GEndo.Endo K
  VerEndoWith = VerEndoWith₀

module UniformFromRuns
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

  module UN =
    Uniform K Input₀ Size₀
      (λ x → decode (DetRun₀ x))
      decode
      (GEndo.idEndo K)
      (GEndo.idEndo K)
      (GEndo.idEndo K)

  open UN public

-- ℕ-bounded “within bound” via a gradeBound map.
-- This lives here (instead of a separate helper module) to keep the core
-- TruthRoute story grade-native while still supporting literature-aligned
-- ℕ-indexed bounds where needed.

module NatLedgerCore
  {ℓ ℓI ℓP ℓC : Level}
  (Input : Set ℓI)
  (Size : Input → ℕ)
  (Code : Set ℓC)
  (Con : Set ℓ)
  (Language : (ℓL : Level) → Set (ℓI ⊔ lsuc (ℓ ⊔ ℓL)))
  (EvalLanguage : ∀ {ℓL} → Language ℓL → Input → Set (ℓ ⊔ ℓL))
  (IsPoly : (ℕ → ℕ) → Set ℓP)
  (FlowAt : ℕ → Con → Con)
  (DetWithin : ∀ {ℓA} (Acc : Con → Set ℓA) → ℕ → Input → Set ℓA)
  (VerWithinWith : ∀ {ℓA} (Acc : Con → Set ℓA) → ℕ → Input → Code → Set ℓA)
  where

  DetPolyTimeBounded : ∀ {ℓA} (Acc : Con → Set ℓA) → Set (ℓI ⊔ ℓP ⊔ ℓA)
  DetPolyTimeBounded Acc =
    Σ (ℕ → ℕ) (λ p →
      IsPoly p
      × (∀ x → DetWithin Acc (p (Size x)) x))

  PolyTotalWitnessedVerification
    : ∀ {ℓA} (Acc : Con → Set ℓA)
    → Set (ℓI ⊔ ℓP ⊔ ℓC ⊔ ℓA)
  PolyTotalWitnessedVerification Acc =
    Σ (ℕ → ℕ) (λ p →
      IsPoly p
      × (∀ x → Σ Code (λ w → VerWithinWith Acc (p (Size x)) x w)))

  -- Super-polynomial hardness of determinism for this Acc predicate.
  SuperPolyHardness : ∀ {ℓA} (Acc : Con → Set ℓA) → Set (ℓI ⊔ ℓP ⊔ ℓA)
  SuperPolyHardness Acc =
    ∀ (p : ℕ → ℕ) → IsPoly p →
      Σ Input (λ x → ¬ (DetWithin Acc (p (Size x)) x))

  noDetPolyTimeBounded
    : ∀ {ℓA} {Acc : Con → Set ℓA}
    → SuperPolyHardness Acc
    → ¬ DetPolyTimeBounded Acc
  noDetPolyTimeBounded sp (p , (polyP , boundD)) =
    let ex = sp p polyP in
    let x  = proj₁ ex in
    let notLe = proj₂ ex in
    ⊥-elim (notLe (boundD x))

  record ETHAssumption {ℓA} (Acc : Con → Set ℓA)
    : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓP ⊔ ℓA))) where
    field
      hard : SuperPolyHardness Acc

  ethNotP : ∀ {ℓA} {Acc : Con → Set ℓA} → ETHAssumption Acc → ¬ DetPolyTimeBounded Acc
  ethNotP {Acc = Acc} A = noDetPolyTimeBounded {Acc = Acc} (ETHAssumption.hard A)

  record SpectralSeparationAssumptions {ℓA} (Acc : Con → Set ℓA)
    : Set (lsuc (lsuc (ℓI ⊔ ℓP ⊔ ℓC ⊔ ℓA))) where
    field
      total-witness : PolyTotalWitnessedVerification Acc
      Det-superpoly : SuperPolyHardness Acc

  record PvsNPClaim {ℓA} (Acc : Con → Set ℓA)
    : Set (lsuc (ℓI ⊔ ℓP ⊔ ℓC ⊔ ℓA)) where
    field
      total-holds : PolyTotalWitnessedVerification Acc
      notP        : ¬ DetPolyTimeBounded Acc

  record PvsNPPack {ℓA} (Acc : Con → Set ℓA) (A : SpectralSeparationAssumptions Acc)
    : Set (lsuc (lsuc (ℓI ⊔ ℓP ⊔ ℓC ⊔ ℓA))) where
    field
      assumptions : SpectralSeparationAssumptions Acc
      claim       : PvsNPClaim Acc

  mkPvsNP : ∀ {ℓA} {Acc : Con → Set ℓA} (A : SpectralSeparationAssumptions Acc) → PvsNPPack Acc A
  mkPvsNP {Acc = Acc} A =
    record
      { assumptions = A
      ; claim = record
          { total-holds = SpectralSeparationAssumptions.total-witness A
          ; notP        = noDetPolyTimeBounded {Acc = Acc} (SpectralSeparationAssumptions.Det-superpoly A)
          }
      }

  -- Standard pack skeleton (uniform API).
  Assumptions = SpectralSeparationAssumptions
  Claim       = PvsNPClaim
  Pack        = PvsNPPack
  mkPack      = mkPvsNP

  record InPBy {ℓL : Level} (L : Language ℓL) (detObs : Input → Con)
    : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓL ⊔ ℓP))) where
    field
      tBound  : ℕ → ℕ
      polyT   : IsPoly tBound

      Acc     : Con → Set (ℓ ⊔ ℓL)
      decAcc  : ∀ c → Acc c ⊎ ¬ (Acc c)

      correct : ∀ x →
        EvalLanguage L x ↔ Acc (FlowAt (tBound (Size x)) (detObs x))

  module WithWitnessSizeBy (WSize₀ : Code → ℕ) (verObsWith : Input → Code → Con) where
    open import LogOS.Prelude.NatOrder using (_≤ℕ_)

    WSize : Code → ℕ
    WSize = WSize₀

    PolyTotalWitnessedVerificationW : ∀ {ℓA} (Acc : Con → Set ℓA) → Set (ℓI ⊔ ℓP ⊔ ℓC ⊔ ℓA)
    PolyTotalWitnessedVerificationW Acc =
      Σ (ℕ → ℕ) (λ t →
        IsPoly t
        × Σ (ℕ → ℕ) (λ wBound →
            IsPoly wBound
            × (∀ x → Σ Code (λ w →
                  (WSize w ≤ℕ wBound (Size x))
                  × VerWithinWith Acc (t (Size x)) x w))))

    -- Forget the witness-size bound.
    forgetW
      : ∀ {ℓA} {Acc : Con → Set ℓA}
      → PolyTotalWitnessedVerificationW Acc
      → PolyTotalWitnessedVerification Acc
    forgetW (t , (polyT , (wBound , (polyW , wit)))) =
      t , (polyT , (λ x → let ex = wit x in proj₁ ex , snd (proj₂ ex)))

    record SpectralSeparationAssumptionsW {ℓA} (Acc : Con → Set ℓA)
      : Set (lsuc (lsuc (ℓI ⊔ ℓP ⊔ ℓC ⊔ ℓA))) where
      field
        total-witnessW : PolyTotalWitnessedVerificationW Acc
        Det-superpoly  : SuperPolyHardness Acc

    record PvsNPClaimW {ℓA} (Acc : Con → Set ℓA)
      : Set (lsuc (ℓI ⊔ ℓP ⊔ ℓC ⊔ ℓA)) where
      field
        total-holdsW : PolyTotalWitnessedVerificationW Acc
        notP         : ¬ DetPolyTimeBounded Acc

    record PvsNPPackW {ℓA} (Acc : Con → Set ℓA) (A : SpectralSeparationAssumptionsW Acc)
      : Set (lsuc (lsuc (ℓI ⊔ ℓP ⊔ ℓC ⊔ ℓA))) where
      field
        assumptions : SpectralSeparationAssumptionsW Acc
        claim       : PvsNPClaimW Acc

    mkPvsNPW : ∀ {ℓA} {Acc : Con → Set ℓA} (A : SpectralSeparationAssumptionsW Acc) → PvsNPPackW Acc A
    mkPvsNPW {Acc = Acc} A =
      record
        { assumptions = A
        ; claim = record
            { total-holdsW = SpectralSeparationAssumptionsW.total-witnessW A
            ; notP         = noDetPolyTimeBounded {Acc = Acc} (SpectralSeparationAssumptionsW.Det-superpoly A)
            }
        }

    -- Standard pack skeleton (uniform API), witness-size variant.
    AssumptionsW = SpectralSeparationAssumptionsW
    ClaimW       = PvsNPClaimW
    PackW        = PvsNPPackW
    mkPackW      = mkPvsNPW

    record InNPBy {ℓL : Level} (L : Language ℓL)
      : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓL ⊔ ℓP ⊔ ℓC))) where
      field
        wBound  : ℕ → ℕ
        tBound  : ℕ → ℕ
        polyW   : IsPoly wBound
        polyT   : IsPoly tBound

        Acc     : Con → Set (ℓ ⊔ ℓL)
        decAcc  : ∀ c → Acc c ⊎ ¬ (Acc c)

        correct : ∀ x →
          EvalLanguage L x ↔
          Σ Code (λ w →
            (WSize w ≤ℕ wBound (Size x))
            × Acc (FlowAt (tBound (Size x)) (verObsWith x w)))

module NonUniformNat
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

  module N = NonUniform K Input₀ Size₀ DetRun₀ VerRun₀ VerRunWith₀
  open N public using
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

  module Ledger =
    NatLedgerCore Input Size (GradedKernel.Code K) Con Language (λ L x → L x) IsPoly
      (λ t c → Flow (gradeBound t) c)
      DetWithin
      VerWithinWith

  open Ledger public
    using
      ( DetPolyTimeBounded
      ; PolyTotalWitnessedVerification
      ; SuperPolyHardness
      ; noDetPolyTimeBounded
      ; ETHAssumption
      ; ethNotP
      ; SpectralSeparationAssumptions
      ; PvsNPClaim
      ; PvsNPPack
      ; mkPvsNP
      ; Assumptions
      ; Claim
      ; Pack
      ; mkPack
      )

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
    module W = Ledger.WithWitnessSizeBy WSize₀ (λ x w → decodeK (VerRunWith x w))

    open W public
      using
        ( WSize
        ; PolyTotalWitnessedVerificationW
        ; forgetW
        ; SpectralSeparationAssumptionsW
        ; PvsNPClaimW
        ; PvsNPPackW
        ; mkPvsNPW
        ; AssumptionsW
        ; ClaimW
        ; PackW
        ; mkPackW
        )
    open import LogOS.Prelude.NatOrder using (_≤ℕ_)

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

  -- Grade-native polynomial bounds: core route (re-exported from `NonUniform`).
  module GradeBounded = N.GradeBounded

module UniformNat
  {ℓ ℓI ℓP : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (Input₀ : Set ℓI)
  (Size₀  : Input₀ → ℕ)
  (encodeI₀ : Input₀ → ConPreorder.Con (BulkBoundary.bnd (GradedKernel.BB K)))
  (encodeW₀ : GradedKernel.Code K → ConPreorder.Con (BulkBoundary.bnd (GradedKernel.BB K)))
  (DetEndo₀ : GEndo.Endo K)
  (VerEndo₀ : GEndo.Endo K)
  (VerEndoWith₀ : GEndo.Endo K)
  (IsPoly₀ : (ℕ → ℕ) → Set ℓP)
  (gradeBound₀ : ℕ → QAdapter.Scale Q)
  where

  module U =
    Uniform K Input₀ Size₀ encodeI₀ encodeW₀ DetEndo₀ VerEndo₀ VerEndoWith₀
  open U public using
    ( Input; Size; Con; Grade; Flow
    ; AccMono; Flow-mono-grade
    ; DetWithinAt; VerWithinAt; VerWithinWithAt
    ; DetWithinAt-mono; VerWithinAt-mono; VerWithinWithAt-mono
    ; Language; encodeI; encodeW; DetEndo; VerEndo; VerEndoWith; decodeK; VerObsWith
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

  module Ledger =
    NatLedgerCore Input Size (GradedKernel.Code K) Con Language (λ L x → L x) IsPoly
      (λ t c → Flow (gradeBound t) c)
      DetWithin
      VerWithinWith

  open Ledger public
    using
      ( DetPolyTimeBounded
      ; PolyTotalWitnessedVerification
      ; SuperPolyHardness
      ; noDetPolyTimeBounded
      ; ETHAssumption
      ; ethNotP
      ; SpectralSeparationAssumptions
      ; PvsNPClaim
      ; PvsNPPack
      ; mkPvsNP
      ; Assumptions
      ; Claim
      ; Pack
      ; mkPack
      )

  -- Language-relative interface with correctness carried explicitly.

  record InP {ℓL : Level} (L : Language ℓL) : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓL ⊔ ℓP))) where
    field
      tBound  : ℕ → ℕ
      polyT   : IsPoly tBound

      Acc     : Con → Set (ℓ ⊔ ℓL)
      decAcc  : ∀ c → Acc c ⊎ ¬ (Acc c)

      correct : ∀ x →
        L x ↔ Acc (Flow (gradeBound (tBound (Size x))) (encodeI x))

  -- Witness-size refinement (optional layer).

  module WithWitnessSize (WSize₀ : GradedKernel.Code K → ℕ) where
    module W = Ledger.WithWitnessSizeBy WSize₀ (λ x w → U.VerObsWith x w)

    open W public
      using
        ( WSize
        ; PolyTotalWitnessedVerificationW
        ; forgetW
        ; SpectralSeparationAssumptionsW
        ; PvsNPClaimW
        ; PvsNPPackW
        ; mkPvsNPW
        ; AssumptionsW
        ; ClaimW
        ; PackW
        ; mkPackW
        )
    open import LogOS.Prelude.NatOrder using (_≤ℕ_)

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
            × Acc (Flow (gradeBound (tBound (Size x))) (U.VerObsWith x w)))

module UniformNatFromRuns
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

  module UN =
    UniformNat K Input₀ Size₀
      (λ x → decode (DetRun₀ x))
      decode
      (GEndo.idEndo K)
      (GEndo.idEndo K)
      (GEndo.idEndo K)
      IsPoly₀
      gradeBound₀

  open UN public
