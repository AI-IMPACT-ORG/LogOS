{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.ZFC.SetTheory.Derived where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; intro)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

open import LogOS.Prelude.Sum using (_⊎_; inj₁; inj₂)
open import LogOS.Prelude.Product using (Σ; _,_; proj₁; proj₂; _×_)

open import LogOS.Domain.ZFC.SetTheory.Pack using (ZFAxioms)

-- Small derived constructions over any `ZFAxioms` instance.
-- These are “library-level” conveniences that keep downstream code from
-- re-proving the same 2–3 line equivalences.

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} (K : KernelLike Sig Q) (zf : ZFAxioms K) where
  open ZFAxioms zf

  singleton : SetU → SetU
  singleton x = proj₁ (pairing x x)

  mem-singleton↔ : ∀ {x z} → (z ∈ singleton x) ↔ (z ≈ x)
  mem-singleton↔ {x} {z} =
    let p = pairing x x
    in
    intro
      (λ z∈ →
        let e = _↔_.to (proj₂ p z) z∈ in
        elim e)
      (λ zx →
        _↔_.from (proj₂ p z) (inj₁ zx))
    where
      elim : ∀ {A : Set ℓ} → (A ⊎ A) → A
      elim (inj₁ a) = a
      elim (inj₂ a) = a

  union₂ : SetU → SetU → SetU
  union₂ x y = proj₁ (union (proj₁ (pairing x y)))

  -- `z ∈ (x ∪ y)` iff `z ∈ x` or `z ∈ y`.
  mem-union₂↔ : ∀ {x y z} → (z ∈ union₂ x y) ↔ ((z ∈ x) ⊎ (z ∈ y))
  mem-union₂↔ {x} {y} {z} =
    let px = pairing x y
        u  = union (proj₁ px)
    in
    intro
      (λ z∈u →
        let witness = _↔_.to (proj₂ u z) z∈u
            w = proj₁ witness
            (w∈pair , z∈w) = proj₂ witness
            wIs = _↔_.to (proj₂ px w) w∈pair
        in toSum wIs z∈w)
      (λ where
         (inj₁ z∈x) →
           _↔_.from (proj₂ u z)
             ( x
             , ( _↔_.from (proj₂ px x) (inj₁ (refl≈ x))
               , z∈x
               )
             )
         (inj₂ z∈y) →
           _↔_.from (proj₂ u z)
             ( y
             , ( _↔_.from (proj₂ px y) (inj₂ (refl≈ y))
               , z∈y
               )
             )
      )
    where
      toSum : ∀ {w} → (w ≈ x ⊎ w ≈ y) → z ∈ w → (z ∈ x) ⊎ (z ∈ y)
      toSum (inj₁ wx) z∈w =
        inj₁ (_↔_.to (mem-ext wx z) z∈w)
      toSum (inj₂ wy) z∈w =
        inj₂ (_↔_.to (mem-ext wy z) z∈w)
