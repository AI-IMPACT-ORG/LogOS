{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.PhysToTruthRouteBridge where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; proj₁; proj₂; fst; snd)

open import LogOS.Prelude as Eq using (refl; sym; trans; cong)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Algebra.ConAlg
open import LogOS.Kernel.Graded
open import LogOS.Kernel.Graded.Hom
import LogOS.Domain.Complexity.TruthRoute_Grade_Only as TRG
import LogOS.Domain.Complexity.PolyGrade as PG
open import LogOS.Domain.Complexity.Poly using (PolyPred)

-- Grade-reindexing bridge: transport TruthRoute claims across kernels by a grade hom.
-- This is the cost→time (or resource→resource) bridge point.

module For
  {ℓ ℓI ℓP : Level}
  {Sig : LogOSSignature ℓ}
  {Q₁ Q₂ : QAdapter ℓ}
  (K₁ : GradedKernel Sig Q₁)
  (K₂ : GradedKernel Sig Q₂)
  (h  : GradedKernelHomWithGrade K₁ K₂)
  (hf : GradedKernelHomFlowWithGrade K₁ K₂ h)
  (Input : Set ℓI)
  (Size  : Input → ℕ)
  (DetRun₁ : Input → GradedKernel.Code K₁)
  (VerRun₁ : Input → GradedKernel.Code K₁)
  (VerRunWith₁ : Input → GradedKernel.Code K₁ → GradedKernel.Code K₁)
  (DetRun₂ : Input → GradedKernel.Code K₂)
  (VerRun₂ : Input → GradedKernel.Code K₂)
  (VerRunWith₂ : Input → GradedKernel.Code K₂ → GradedKernel.Code K₂)
  (IsPoly : (ℕ → ℕ) → Set ℓP)
  (gradeBound₁ : ℕ → QAdapter.Scale Q₁)
  (gradeBound₂ : ℕ → QAdapter.Scale Q₂)
  (grade-coh : ∀ n →
     gradeBound₂ n ≡
       (let module GH = Truth.GuardedCore.GradeHom (GradedKernelHomWithGrade.grade-hom h) in
        GH.map (gradeBound₁ n)))
  (det-map : ∀ x → GradedKernelHomWithGrade.mapCode h (DetRun₁ x) ≡ DetRun₂ x)
  (ver-map : ∀ x → GradedKernelHomWithGrade.mapCode h (VerRun₁ x) ≡ VerRun₂ x)
  (verw-map : ∀ x w → GradedKernelHomWithGrade.mapCode h (VerRunWith₁ x w)
                     ≡ VerRunWith₂ x (GradedKernelHomWithGrade.mapCode h w))
  where

  module R₁ = TRG.ForNat K₁ Input Size DetRun₁ VerRun₁ VerRunWith₁ IsPoly gradeBound₁
  module R₂ = TRG.ForNat K₂ Input Size DetRun₂ VerRun₂ VerRunWith₂ IsPoly gradeBound₂

  private
    open GradedKernelHomWithGrade h
    module GH = Truth.GuardedCore.GradeHom grade-hom
    open GH renaming (map to grade-map)

  module AT = FlowAccTransportWithGrade K₁ K₂ h hf
  open AT public using (AccBridge)

  -- Transport deterministic “within bound” at a grade.
  mapDetWithinAt
    : ∀ {ℓA₁ ℓA₂} {Acc₁ : R₁.Con → Set ℓA₁} {Acc₂ : R₂.Con → Set ℓA₂}
      (AB : AccBridge Acc₁ Acc₂)
      → ∀ g x → R₁.DetWithinAt Acc₁ g x → R₂.DetWithinAt Acc₂ (grade-map g) x
  mapDetWithinAt AB g x acc =
    let
      c₁ = R₁.decodeK (DetRun₁ x)
      eqDet : R₂.decodeK (DetRun₂ x) ≡ ConAlgHom≡.map∂ (GradedKernelHomWithGrade.con-hom h) c₁
      eqDet =
        trans (cong R₂.decodeK (sym (det-map x)))
              (GradedKernelHomWithGrade.map-decode h (DetRun₁ x))
    in
    AT.mapFlowAccAt-subst AB g c₁ (R₂.decodeK (DetRun₂ x)) eqDet acc

  -- Transport deterministic “within bound” at an ℕ bound.
  mapDetWithin
    : ∀ {ℓA₁ ℓA₂} {Acc₁ : R₁.Con → Set ℓA₁} {Acc₂ : R₂.Con → Set ℓA₂}
      (AB : AccBridge Acc₁ Acc₂)
      → ∀ t x → R₁.DetWithin Acc₁ t x → R₂.DetWithin Acc₂ t x
  mapDetWithin {Acc₂ = Acc₂} AB t x acc =
    Eq.subst
      (λ g → R₂.DetWithinAt Acc₂ g x)
      (Eq.sym (grade-coh t))
      (mapDetWithinAt AB (gradeBound₁ t) x acc)

  mapDetWithinAt-back
    : ∀ {ℓA₁ ℓA₂} {Acc₁ : R₁.Con → Set ℓA₁} {Acc₂ : R₂.Con → Set ℓA₂}
      (AB : AccBridge Acc₁ Acc₂)
      → ∀ g x → R₂.DetWithinAt Acc₂ (grade-map g) x → R₁.DetWithinAt Acc₁ g x
  mapDetWithinAt-back AB g x acc₂ =
    let
      c₁ = R₁.decodeK (DetRun₁ x)
      eqDet : R₂.decodeK (DetRun₂ x) ≡ ConAlgHom≡.map∂ (GradedKernelHomWithGrade.con-hom h) c₁
      eqDet =
        trans (cong R₂.decodeK (sym (det-map x)))
              (GradedKernelHomWithGrade.map-decode h (DetRun₁ x))
    in
    AT.mapFlowAccAt-back-subst AB g c₁ (R₂.decodeK (DetRun₂ x)) eqDet acc₂

  mapDetWithin-back
    : ∀ {ℓA₁ ℓA₂} {Acc₁ : R₁.Con → Set ℓA₁} {Acc₂ : R₂.Con → Set ℓA₂}
      (AB : AccBridge Acc₁ Acc₂)
      → ∀ t x → R₂.DetWithin Acc₂ t x → R₁.DetWithin Acc₁ t x
  mapDetWithin-back {Acc₁ = Acc₁} {Acc₂ = Acc₂} AB t x acc =
    mapDetWithinAt-back AB (gradeBound₁ t) x
      (Eq.subst
         (λ g → R₂.DetWithinAt Acc₂ g x)
         (grade-coh t)
         acc)

  -- Transport verifier “within bound”.
  mapVerWithinWithAt
    : ∀ {ℓA₁ ℓA₂} {Acc₁ : R₁.Con → Set ℓA₁} {Acc₂ : R₂.Con → Set ℓA₂}
      (AB : AccBridge Acc₁ Acc₂)
      → ∀ g x w → R₁.VerWithinWithAt Acc₁ g x w →
                  R₂.VerWithinWithAt Acc₂ (grade-map g) x (mapCode w)
  mapVerWithinWithAt AB g x w acc =
    let
      c₁ = R₁.decodeK (VerRunWith₁ x w)
      eqVer : R₂.decodeK (VerRunWith₂ x (mapCode w))
             ≡ ConAlgHom≡.map∂ (GradedKernelHomWithGrade.con-hom h) c₁
      eqVer =
        trans (cong R₂.decodeK (sym (verw-map x w)))
              (GradedKernelHomWithGrade.map-decode h (VerRunWith₁ x w))
    in
    AT.mapFlowAccAt-subst AB g c₁ (R₂.decodeK (VerRunWith₂ x (mapCode w))) eqVer acc

  mapVerWithinWith
    : ∀ {ℓA₁ ℓA₂} {Acc₁ : R₁.Con → Set ℓA₁} {Acc₂ : R₂.Con → Set ℓA₂}
      (AB : AccBridge Acc₁ Acc₂)
      → ∀ t x w → R₁.VerWithinWith Acc₁ t x w →
                  R₂.VerWithinWith Acc₂ t x (mapCode w)
  mapVerWithinWith {Acc₂ = Acc₂} AB t x w acc =
    Eq.subst
      (λ g → R₂.VerWithinWithAt Acc₂ g x (mapCode w))
      (Eq.sym (grade-coh t))
      (mapVerWithinWithAt AB (gradeBound₁ t) x w acc)

  -- Transport the NP-style witness pack.
  mapNP
    : ∀ {ℓA₁ ℓA₂} {Acc₁ : R₁.Con → Set ℓA₁} {Acc₂ : R₂.Con → Set ℓA₂}
      (AB : AccBridge Acc₁ Acc₂)
      → R₁.PolyWitnessedTotalVerification Acc₁
      → R₂.PolyWitnessedTotalVerification Acc₂
  mapNP AB (p , (polyP , wit)) =
    p , (polyP , (λ x →
      let ex = wit x in
      let w  = proj₁ ex in
      mapCode w , mapVerWithinWith AB (p (Size x)) x w (proj₂ ex)))

  -- Transport deterministic super-polynomial hardness.
  mapSuperPolyHardness
    : ∀ {ℓA₁ ℓA₂} {Acc₁ : R₁.Con → Set ℓA₁} {Acc₂ : R₂.Con → Set ℓA₂}
      (AB : AccBridge Acc₁ Acc₂)
      → R₁.SuperPolyHardness Acc₁
      → R₂.SuperPolyHardness Acc₂
  mapSuperPolyHardness AB sp p polyP =
    let ex = sp p polyP in
    let x  = proj₁ ex in
    x , λ within →
          proj₂ ex (mapDetWithin-back AB (p (Size x)) x within)

  -- Transport the full separation assumptions and build the claim on K₂.
  mapAssumptions
    : ∀ {ℓA₁ ℓA₂} {Acc₁ : R₁.Con → Set ℓA₁} {Acc₂ : R₂.Con → Set ℓA₂}
      (AB : AccBridge Acc₁ Acc₂)
      → R₁.SpectralSeparationAssumptions Acc₁
      → R₂.SpectralSeparationAssumptions Acc₂
  mapAssumptions AB A =
    record
      { NP-witness   = mapNP AB (R₁.SpectralSeparationAssumptions.NP-witness A)
      ; Det-superpoly = mapSuperPolyHardness AB (R₁.SpectralSeparationAssumptions.Det-superpoly A)
      }

  mapPvsNP
    : ∀ {ℓA₁ ℓA₂} {Acc₁ : R₁.Con → Set ℓA₁} {Acc₂ : R₂.Con → Set ℓA₂}
      (AB : AccBridge Acc₁ Acc₂)
      → R₁.SpectralSeparationAssumptions Acc₁
      → R₂.PvsNPClaim Acc₂
  mapPvsNP AB A =
    R₂.PvsNPPack.claim (R₂.mkPvsNP (mapAssumptions AB A))

-- Grade-native bridge: transport TruthRoute_Grade_Only claims across kernels by a grade hom.

module ForG
  {ℓ ℓI : Level}
  {Sig : LogOSSignature ℓ}
  {Q₁ Q₂ : QAdapter ℓ}
  (K₁ : GradedKernel Sig Q₁)
  (K₂ : GradedKernel Sig Q₂)
  (h  : GradedKernelHomWithGrade K₁ K₂)
  (hf : GradedKernelHomFlowWithGrade K₁ K₂ h)
  (Input : Set ℓI)
  (Size  : Input → ℕ)
  (DetRun₁ : Input → GradedKernel.Code K₁)
  (VerRun₁ : Input → GradedKernel.Code K₁)
  (VerRunWith₁ : Input → GradedKernel.Code K₁ → GradedKernel.Code K₁)
  (DetRun₂ : Input → GradedKernel.Code K₂)
  (VerRun₂ : Input → GradedKernel.Code K₂)
  (VerRunWith₂ : Input → GradedKernel.Code K₂ → GradedKernel.Code K₂)
  (PG₁ : PG.PolyPredG (QAdapter.Scale Q₁))
  (PG₂ : PG.PolyPredG (QAdapter.Scale Q₂))
  (poly-map : ∀ g → PG.PolyPredG.isPolyG PG₁ g →
                PG.PolyPredG.isPolyG PG₂
                  (λ n →
                    let module GH = Truth.GuardedCore.GradeHom (GradedKernelHomWithGrade.grade-hom h) in
                    GH.map (g n)))
  (poly-back : ∀ g → PG.PolyPredG.isPolyG PG₂ g →
                  Σ (ℕ → QAdapter.Scale Q₁) (λ g₁ →
                    PG.PolyPredG.isPolyG PG₁ g₁
                    × (∀ n →
                        g n ≡
                          (let module GH = Truth.GuardedCore.GradeHom (GradedKernelHomWithGrade.grade-hom h) in
                           GH.map (g₁ n)))))
  (det-map : ∀ x → GradedKernelHomWithGrade.mapCode h (DetRun₁ x) ≡ DetRun₂ x)
  (ver-map : ∀ x → GradedKernelHomWithGrade.mapCode h (VerRun₁ x) ≡ VerRun₂ x)
  (verw-map : ∀ x w → GradedKernelHomWithGrade.mapCode h (VerRunWith₁ x w)
                     ≡ VerRunWith₂ x (GradedKernelHomWithGrade.mapCode h w))
  where

  module R₁ = TRG.For K₁ Input Size DetRun₁ VerRun₁ VerRunWith₁
  module R₂ = TRG.For K₂ Input Size DetRun₂ VerRun₂ VerRunWith₂
  module G₁ = R₁.GradeBounded PG₁
  module G₂ = R₂.GradeBounded PG₂

  private
    open GradedKernelHomWithGrade h
    module GH = Truth.GuardedCore.GradeHom grade-hom
    open GH renaming (map to grade-map)
  module AT = FlowAccTransportWithGrade K₁ K₂ h hf
  open AT public using (AccBridge)

  mapDetWithinAt
    : ∀ {ℓA₁ ℓA₂} {Acc₁ : R₁.Con → Set ℓA₁} {Acc₂ : R₂.Con → Set ℓA₂}
      (AB : AccBridge Acc₁ Acc₂)
      → ∀ g x → R₁.DetWithinAt Acc₁ g x → R₂.DetWithinAt Acc₂ (grade-map g) x
  mapDetWithinAt AB g x acc =
    let
      c₁ = R₁.decodeK (DetRun₁ x)
      eqDet : R₂.decodeK (DetRun₂ x) ≡ ConAlgHom≡.map∂ (GradedKernelHomWithGrade.con-hom h) c₁
      eqDet =
        trans (cong R₂.decodeK (sym (det-map x)))
              (GradedKernelHomWithGrade.map-decode h (DetRun₁ x))
    in
    AT.mapFlowAccAt-subst AB g c₁ (R₂.decodeK (DetRun₂ x)) eqDet acc

  mapDetWithinAt-back
    : ∀ {ℓA₁ ℓA₂} {Acc₁ : R₁.Con → Set ℓA₁} {Acc₂ : R₂.Con → Set ℓA₂}
      (AB : AccBridge Acc₁ Acc₂)
      → ∀ g x → R₂.DetWithinAt Acc₂ (grade-map g) x → R₁.DetWithinAt Acc₁ g x
  mapDetWithinAt-back AB g x acc₂ =
    let
      c₁ = R₁.decodeK (DetRun₁ x)
      eqDet : R₂.decodeK (DetRun₂ x) ≡ ConAlgHom≡.map∂ (GradedKernelHomWithGrade.con-hom h) c₁
      eqDet =
        trans (cong R₂.decodeK (sym (det-map x)))
              (GradedKernelHomWithGrade.map-decode h (DetRun₁ x))
    in
    AT.mapFlowAccAt-back-subst AB g c₁ (R₂.decodeK (DetRun₂ x)) eqDet acc₂

  mapVerWithinWithAt
    : ∀ {ℓA₁ ℓA₂} {Acc₁ : R₁.Con → Set ℓA₁} {Acc₂ : R₂.Con → Set ℓA₂}
      (AB : AccBridge Acc₁ Acc₂)
      → ∀ g x w → R₁.VerWithinWithAt Acc₁ g x w →
                  R₂.VerWithinWithAt Acc₂ (grade-map g) x (mapCode w)
  mapVerWithinWithAt AB g x w acc =
    let
      c₁ = R₁.decodeK (VerRunWith₁ x w)
      eqVer : R₂.decodeK (VerRunWith₂ x (mapCode w))
             ≡ ConAlgHom≡.map∂ (GradedKernelHomWithGrade.con-hom h) c₁
      eqVer =
        trans (cong R₂.decodeK (sym (verw-map x w)))
              (GradedKernelHomWithGrade.map-decode h (VerRunWith₁ x w))
    in
    AT.mapFlowAccAt-subst AB g c₁ (R₂.decodeK (VerRunWith₂ x (mapCode w))) eqVer acc

  mapNP
    : ∀ {ℓA₁ ℓA₂} {Acc₁ : R₁.Con → Set ℓA₁} {Acc₂ : R₂.Con → Set ℓA₂}
      (AB : AccBridge Acc₁ Acc₂)
      → G₁.PolyWitnessedTotalVerificationG Acc₁
      → G₂.PolyWitnessedTotalVerificationG Acc₂
  mapNP AB (g , (polyG , wit)) =
    (λ n → grade-map (g n)) ,
    (poly-map g polyG , (λ x →
      let ex = wit x in
      let w  = proj₁ ex in
      mapCode w , mapVerWithinWithAt AB (g (Size x)) x w (proj₂ ex)))

  mapSuperPolyHardness
    : ∀ {ℓA₁ ℓA₂} {Acc₁ : R₁.Con → Set ℓA₁} {Acc₂ : R₂.Con → Set ℓA₂}
      (AB : AccBridge Acc₁ Acc₂)
      → G₁.SuperPolyHardnessG Acc₁
      → G₂.SuperPolyHardnessG Acc₂
  mapSuperPolyHardness {Acc₂ = Acc₂} AB sp g₂ polyG₂ =
    let back = poly-back g₂ polyG₂ in
    let g₁ = proj₁ back in
    let polyG₁ = fst (proj₂ back) in
    let eqg = snd (proj₂ back) in
    let ex = sp g₁ polyG₁ in
    let x  = proj₁ ex in
    x , λ within →
          let
            within' : R₂.DetWithinAt Acc₂ (grade-map (g₁ (Size x))) x
            within' =
              Eq.subst
                (λ g → R₂.DetWithinAt Acc₂ g x)
                (eqg (Size x))
                within
          in
          proj₂ ex (mapDetWithinAt-back AB (g₁ (Size x)) x within')

  mapAssumptions
    : ∀ {ℓA₁ ℓA₂} {Acc₁ : R₁.Con → Set ℓA₁} {Acc₂ : R₂.Con → Set ℓA₂}
      (AB : AccBridge Acc₁ Acc₂)
      → G₁.SpectralSeparationAssumptionsG Acc₁
      → G₂.SpectralSeparationAssumptionsG Acc₂
  mapAssumptions AB A =
    record
      { NP-witnessG   = mapNP AB (G₁.SpectralSeparationAssumptionsG.NP-witnessG A)
      ; Det-superpolyG = mapSuperPolyHardness AB (G₁.SpectralSeparationAssumptionsG.Det-superpolyG A)
      }

  mapPvsNP
    : ∀ {ℓA₁ ℓA₂} {Acc₁ : R₁.Con → Set ℓA₁} {Acc₂ : R₂.Con → Set ℓA₂}
      (AB : AccBridge Acc₁ Acc₂)
      → G₁.SpectralSeparationAssumptionsG Acc₁
      → G₂.PvsNPClaimG Acc₂
  mapPvsNP AB A =
    G₂.PvsNPPackG.claim (G₂.mkPvsNPG (mapAssumptions AB A))

-- Convenience wrappers: discharge poly-map/poly-back via PolyGrade lemmas.

module ForGSection
  {ℓ ℓI : Level}
  {Sig : LogOSSignature ℓ}
  {Q₁ Q₂ : QAdapter ℓ}
  (K₁ : GradedKernel Sig Q₁)
  (K₂ : GradedKernel Sig Q₂)
  (h  : GradedKernelHomWithGrade K₁ K₂)
  (hf : GradedKernelHomFlowWithGrade K₁ K₂ h)
  (Input : Set ℓI)
  (Size  : Input → ℕ)
  (DetRun₁ : Input → GradedKernel.Code K₁)
  (VerRun₁ : Input → GradedKernel.Code K₁)
  (VerRunWith₁ : Input → GradedKernel.Code K₁ → GradedKernel.Code K₁)
  (DetRun₂ : Input → GradedKernel.Code K₂)
  (VerRun₂ : Input → GradedKernel.Code K₂)
  (VerRunWith₂ : Input → GradedKernel.Code K₂ → GradedKernel.Code K₂)
  (PG₁ : PG.PolyPredG (QAdapter.Scale Q₁))
  (PG₂ : PG.PolyPredG (QAdapter.Scale Q₂))
  (poly-map : ∀ g → PG.PolyPredG.isPolyG PG₁ g →
                PG.PolyPredG.isPolyG PG₂
                  (λ n →
                    let module GH = Truth.GuardedCore.GradeHom (GradedKernelHomWithGrade.grade-hom h) in
                    GH.map (g n)))
  (back : QAdapter.Scale Q₂ → QAdapter.Scale Q₁)
  (map-back : ∀ g₂ →
     (let module GH = Truth.GuardedCore.GradeHom (GradedKernelHomWithGrade.grade-hom h) in
      GH.map (back g₂)) ≡ g₂)
  (poly-back : ∀ g₂ → PG.PolyPredG.isPolyG PG₂ g₂ →
                  PG.PolyPredG.isPolyG PG₁ (λ n → back (g₂ n)))
  (det-map : ∀ x → GradedKernelHomWithGrade.mapCode h (DetRun₁ x) ≡ DetRun₂ x)
  (ver-map : ∀ x → GradedKernelHomWithGrade.mapCode h (VerRun₁ x) ≡ VerRun₂ x)
  (verw-map : ∀ x w → GradedKernelHomWithGrade.mapCode h (VerRunWith₁ x w)
                     ≡ VerRunWith₂ x (GradedKernelHomWithGrade.mapCode h w))
  where

  private
    module GH = Truth.GuardedCore.GradeHom (GradedKernelHomWithGrade.grade-hom h)
    open GH renaming (map to grade-map)
    module PH = PG.Hom PG₁ PG₂
    module Sec = PH.Section grade-map back map-back poly-back

  module Core =
    ForG K₁ K₂ h hf Input Size DetRun₁ VerRun₁ VerRunWith₁
         DetRun₂ VerRun₂ VerRunWith₂
         PG₁ PG₂ poly-map Sec.poly-back-section
         det-map ver-map verw-map

  open Core public

module ForGFromNat
  {ℓ ℓI : Level}
  {Sig : LogOSSignature ℓ}
  {Q₁ Q₂ : QAdapter ℓ}
  (K₁ : GradedKernel Sig Q₁)
  (K₂ : GradedKernel Sig Q₂)
  (h  : GradedKernelHomWithGrade K₁ K₂)
  (hf : GradedKernelHomFlowWithGrade K₁ K₂ h)
  (Input : Set ℓI)
  (Size  : Input → ℕ)
  (DetRun₁ : Input → GradedKernel.Code K₁)
  (VerRun₁ : Input → GradedKernel.Code K₁)
  (VerRunWith₁ : Input → GradedKernel.Code K₁ → GradedKernel.Code K₁)
  (DetRun₂ : Input → GradedKernel.Code K₂)
  (VerRun₂ : Input → GradedKernel.Code K₂)
  (VerRunWith₂ : Input → GradedKernel.Code K₂ → GradedKernel.Code K₂)
  (Pℕ : PolyPred)
  (gradeBound₁ : ℕ → QAdapter.Scale Q₁)
  (gradeBound₂ : ℕ → QAdapter.Scale Q₂)
  (grade-coh : ∀ n →
     gradeBound₂ n ≡
       (let module GH = Truth.GuardedCore.GradeHom (GradedKernelHomWithGrade.grade-hom h) in
        GH.map (gradeBound₁ n)))
  (det-map : ∀ x → GradedKernelHomWithGrade.mapCode h (DetRun₁ x) ≡ DetRun₂ x)
  (ver-map : ∀ x → GradedKernelHomWithGrade.mapCode h (VerRun₁ x) ≡ VerRun₂ x)
  (verw-map : ∀ x w → GradedKernelHomWithGrade.mapCode h (VerRunWith₁ x w)
                     ≡ VerRunWith₂ x (GradedKernelHomWithGrade.mapCode h w))
  where

  module PG₁ = PG.FromNat Q₁ Pℕ gradeBound₁
  module PG₂ = PG.FromNat Q₂ Pℕ gradeBound₂

  private
    module GH = Truth.GuardedCore.GradeHom (GradedKernelHomWithGrade.grade-hom h)
    open GH renaming (map to grade-map)
    module PolyMap =
      PG.FromNatHom Q₁ Q₂ Pℕ gradeBound₁ gradeBound₂
        (GradedKernelHomWithGrade.grade-hom h) grade-coh

  module WithBack
    (back : QAdapter.Scale Q₂ → QAdapter.Scale Q₁)
    (map-back : ∀ g₂ → grade-map (back g₂) ≡ g₂)
    (poly-back : ∀ g₂ → PG.PolyPredG.isPolyG PG₂.polyPredG g₂ →
                    PG.PolyPredG.isPolyG PG₁.polyPredG (λ n → back (g₂ n)))
    where

    module PH = PG.Hom PG₁.polyPredG PG₂.polyPredG
    module Sec = PH.Section grade-map back map-back poly-back

    module Core =
      ForG K₁ K₂ h hf Input Size DetRun₁ VerRun₁ VerRunWith₁
           DetRun₂ VerRun₂ VerRunWith₂
           PG₁.polyPredG PG₂.polyPredG
           PolyMap.poly-map Sec.poly-back-section
           det-map ver-map verw-map

    open Core public
