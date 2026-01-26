{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.PolyGrade where

open import LogOS.Prelude

open import LogOS.Prelude.Nat using (ℕ)
open import LogOS.Prelude.Product using (Σ; _,_; _×_)

open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Truth as Truth
open import LogOS.Domain.Complexity.Poly using (PolyPred)

-- Grade-native polynomial predicate: a property of grade-bound functions.
record PolyPredG {ℓG : Level} (Grade : Set ℓG) : Set (lsuc ℓG) where
  field
    isPolyG : (ℕ → Grade) → Set ℓG

-- Compatibility: lift an ℕ-polynomial predicate through a grade bound.
module FromNat
  {ℓQ : Level}
  (Q : QAdapter ℓQ)
  (Pℕ : PolyPred)
  (gradeBound : ℕ → QAdapter.Scale Q)
  where

  open QAdapter Q renaming (Scale to Grade; _≤s_ to _≤g_)
  open PolyPred Pℕ using (isPoly)

  polyPredG : PolyPredG Grade
  polyPredG =
    record
      { isPolyG = λ g →
          Σ (ℕ → ℕ) (λ p →
            isPoly p × (∀ n → _≤g_ (g n) (gradeBound (p n))))
      }

-- Small lemma pack: transporting grade-polynomials along grade maps.
module Hom
  {ℓG₁ ℓG₂ : Level}
  {Grade₁ : Set ℓG₁}
  {Grade₂ : Set ℓG₂}
  (PG₁ : PolyPredG Grade₁)
  (PG₂ : PolyPredG Grade₂)
  where

  open PolyPredG PG₁ renaming (isPolyG to IsPolyG₁)
  open PolyPredG PG₂ renaming (isPolyG to IsPolyG₂)

  -- Identity map (standard grade hom).
  poly-map-id : ∀ g → IsPolyG₁ g → IsPolyG₁ g
  poly-map-id _ pg = pg

  poly-back-id
    : ∀ g → IsPolyG₁ g
      → Σ (ℕ → Grade₁) (λ g₁ → IsPolyG₁ g₁ × (∀ n → g n ≡ g₁ n))
  poly-back-id g pg = g , (pg , (λ _ → refl))

  -- Section-based back-transport (standard grade hom with a right inverse).
  module Section
    (map : Grade₁ → Grade₂)
    (back : Grade₂ → Grade₁)
    (map-back : ∀ g₂ → map (back g₂) ≡ g₂)
    (poly-back : ∀ g₂ → IsPolyG₂ g₂ → IsPolyG₁ (λ n → back (g₂ n)))
    where

    poly-back-section
      : ∀ g₂ → IsPolyG₂ g₂
        → Σ (ℕ → Grade₁)
            (λ g₁ → IsPolyG₁ g₁ × (∀ n → g₂ n ≡ map (g₁ n)))
    poly-back-section g₂ polyG₂ =
      (λ n → back (g₂ n)) ,
      (poly-back g₂ polyG₂ , (λ n → sym (map-back (g₂ n))))

-- FromNat + GradeHom: derive a forward poly-map from gradeBound coherence.
module FromNatHom
  {ℓQ : Level}
  (Q₁ Q₂ : QAdapter ℓQ)
  (Pℕ : PolyPred)
  (gradeBound₁ : ℕ → QAdapter.Scale Q₁)
  (gradeBound₂ : ℕ → QAdapter.Scale Q₂)
  (φ : Truth.GuardedCore.GradeHom Q₁ Q₂)
  (grade-coh : ∀ n →
     gradeBound₂ n ≡
       (let module GH = Truth.GuardedCore.GradeHom φ in
        GH.map (gradeBound₁ n)))
  where

  module P₁ = FromNat Q₁ Pℕ gradeBound₁
  module P₂ = FromNat Q₂ Pℕ gradeBound₂

  open QAdapter Q₁ renaming (_≤s_ to _≤g₁_)
  open QAdapter Q₂ renaming (_≤s_ to _≤g₂_)
  open Truth.GuardedCore.GradeHom φ renaming (map to grade-map; mono to grade-mono)
  open PolyPredG P₁.polyPredG renaming (isPolyG to IsPolyG₁)
  open PolyPredG P₂.polyPredG renaming (isPolyG to IsPolyG₂)

  poly-map
    : ∀ g → IsPolyG₁ g → IsPolyG₂ (λ n → grade-map (g n))
  poly-map g (p , (polyP , bound)) =
    p , (polyP , (λ n →
      let le = grade-mono (bound n) in
      subst (λ x → _≤g₂_ (grade-map (g n)) x) (sym (grade-coh (p n))) le))
