{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.ProofSearchCapstoneGraded where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_; _↔_)

open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; fst; snd)

open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Domain.Complexity.Poly using (PolyPred)
import LogOS.Domain.Complexity.ProofSearchBoundary as B
import LogOS.Domain.Complexity.ResourceSchemaGraded as RS

-- Capstone statement (grade-native Route B):
-- unbounded proof search is blocked by a grade-bounded resource bottleneck.

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

  -- The colimit of bounded proof-search along a schedule `sched`.
  ColimProv : ∀ (PS : PB.ProofSystem) (sched : ℕ → ℕ) → Input → Set ℓ
  ColimProv PS sched x = Σ ℕ (λ n → PB.Prov≤ PS (sched n) x)

  -- Cofinal-limit equivalence: Prov∞ is exactly the colimit of Prov≤ along any cofinal sched.
  prov∞↔colim
    : ∀ (PS : PB.ProofSystem) (sched : ℕ → ℕ)
      → PB.Cofinal sched
      → ∀ x → PB.Prov∞ PS x ↔ ColimProv PS sched x
  prov∞↔colim PS sched cof x =
    record
      { to   = λ pr∞ → PB.Prov∞→colim {PS = PS} sched cof x pr∞
      ; from = λ col → PB.bounded→unbounded {PS = PS} (proj₂ col)
      }

  -- Completeness gives P ↔ Prov∞.
  P↔Prov∞ : ∀ {PS : PB.ProofSystem} → PB.Complete PS → ∀ x → P x ↔ PB.Prov∞ PS x
  P↔Prov∞ {PS} C x =
    record
      { to   = PB.P→Prov∞ C x
      ; from = PB.Prov∞→P PS x
      }

  -- Transport a grade/time decider along P ↔ Prov∞ (keeping time/meas/bounds intact).
  toProv∞Decider
    : ∀ {PS : PB.ProofSystem}
      → (C : PB.Complete PS)
      → R.QTimeDecider P
      → R.QTimeDecider (PB.Prov∞ PS)
  toProv∞Decider {PS} C =
    R.mapQTimeDecider (P↔Prov∞ {PS = PS} C)

  -- Grade-bound decider variant (no ℕ-polynomial wrapper).
  toProv∞DeciderG
    : ∀ {PS : PB.ProofSystem}
      → (C : PB.Complete PS)
      → R.QTimeDeciderG P
      → R.QTimeDeciderG (PB.Prov∞ PS)
  toProv∞DeciderG {PS} C =
    R.mapQTimeDeciderG (P↔Prov∞ {PS = PS} C)

  -- Main consequence: hardness for Prov∞ blocks any poly-budget decider for P as well.
  notPolyTime-P
    : ∀ {PS : PB.ProofSystem}
      → (C : PB.Complete PS)
      → (TH : R.Throughput)
      → (CP : R.Capacity)
      → R.Hard (PB.Prov∞ PS) TH CP
      → ¬ (Σ (R.QTimeDecider P) (λ _ → ⊤ {ℓ = lzero}))
  notPolyTime-P {PS} C TH CP hard (qd , u) =
    let contra : ¬ (Σ (R.QTimeDecider (PB.Prov∞ PS)) (λ _ → ⊤ {ℓ = lzero}))
        contra = R.notPolyTime TH CP hard
    in
    contra ((toProv∞Decider C qd) , u)

  -- Grade-bound variant: hardness blocks any grade-bounded decider for P.
  notTimeBoundedG-P
    : ∀ {PS : PB.ProofSystem}
      → (C : PB.Complete PS)
      → (TH : R.ThroughputG)
      → (CP : R.CapacityG)
      → R.HardG (PB.Prov∞ PS) TH CP
      → ¬ (Σ (R.QTimeDeciderG P) (λ _ → ⊤ {ℓ = lzero}))
  notTimeBoundedG-P {PS} C TH CP hard (qd , u) =
    let contra : ¬ (Σ (R.QTimeDeciderG (PB.Prov∞ PS)) (λ _ → ⊤ {ℓ = lzero}))
        contra = R.notTimeBoundedG TH CP hard
    in
    contra ((toProv∞DeciderG C qd) , u)

-- DetWithin route (kernel-friendly abstraction):
-- parameterize by a predicate-indexed “within bound” relation and monotonicity.

module DetWithinRoute
  {ℓI ℓ ℓP ℓD : Level}
  (Input : Set ℓI)
  (size  : Input → ℕ)
  (IsPoly : (ℕ → ℕ) → Set ℓP)
  (P      : Input → Set ℓ)
  (DetWithin : (Input → Set ℓ) → ℕ → Input → Set ℓD)
  (monoDetWithin
     : ∀ {P Q} → (∀ x → P x → Q x)
       → ∀ t x → DetWithin P t x → DetWithin Q t x)
  where

  module PB = B.For {ℓI = ℓI} {ℓ = ℓ} Input P

  DetPolyTimeBounded : (Input → Set ℓ) → Set (ℓI ⊔ ℓP ⊔ ℓD)
  DetPolyTimeBounded L =
    Σ (ℕ → ℕ) (λ p →
      IsPoly p
      × (∀ x → DetWithin L (p (size x)) x))

  SuperPolyHardness : (Input → Set ℓ) → Set (ℓI ⊔ ℓP ⊔ ℓD)
  SuperPolyHardness L =
    ∀ (p : ℕ → ℕ) → IsPoly p →
      Σ Input (λ x → ¬ (DetWithin L (p (size x)) x))

  noDetPolyTimeBounded : ∀ {L} → SuperPolyHardness L → ¬ DetPolyTimeBounded L
  noDetPolyTimeBounded sp (p , (polyP , within)) =
    let ex = sp p polyP in
    proj₂ ex (within (proj₁ ex))

  notDetPolyTime-P
    : ∀ {PS : PB.ProofSystem}
      → PB.Complete PS
      → SuperPolyHardness (PB.Prov∞ PS)
      → ¬ DetPolyTimeBounded P
  notDetPolyTime-P {PS} C sp (p , (polyP , withinP)) =
    let withinProv∞ : ∀ x → DetWithin (PB.Prov∞ PS) (p (size x)) x
        withinProv∞ x =
          monoDetWithin (λ x px → PB.P→Prov∞ C x px) (p (size x)) x (withinP x)
    in
    noDetPolyTimeBounded sp (p , (polyP , withinProv∞))
