{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.ZFC.SetTheory.FormulaPack where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; ¬_; intro)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.API.Kernel
open import LogOS.API.Kernel.Eq using (module ForKernel)

open import LogOS.Prelude using (Σ; _,_; _×_)
open import LogOS.Prelude using (_⊎_)
open import LogOS.ZFC.SetTheory.ChoiceAxiom as AC using (AxiomOfChoice)

-- Metamath-style presentation of the ZFC schemata:
-- Separation/Replacement range over *formulas* (here: `Code`) together with an
-- explicit satisfaction relation (`Pred` / `Rel`), rather than over arbitrary
-- Agda predicates/functions.
--
-- This is “full first-order ZFC as schemata”, without impredicative meta-level
-- quantification. It is the natural interface for a proof assistant.

record ZFAxiomsᶠ {ℓ}
                 {Sig : LogOSSignature ℓ}
                 {Q   : QAdapter ℓ}
                 (K   : Kernel Sig Q)
                 : Set (lsuc (lsuc ℓ)) where
  open Kernel K
  open ForKernel K
  field
    SetU   : Set ℓ
    _∈_    : SetU → SetU → Set ℓ

  -- Membership-induced observational preorder/equality.
  infix 4 _∈_ _⊑_ _≈_
  _⊑_ : SetU → SetU → Set ℓ
  x ⊑ y = ∀ z → (z ∈ x) → (z ∈ y)

  _≈_ : SetU → SetU → Set ℓ
  x ≈ y = (x ⊑ y) × (y ⊑ x)

  refl≈  : ∀ x → x ≈ x
  refl≈ _ = (λ _ zx → zx) , (λ _ zy → zy)

  sym≈   : ∀ {x y} → x ≈ y → y ≈ x
  sym≈ (xy , yx) = (yx , xy)

  trans≈ : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
  trans≈ (xy , yx) (yz , zy) =
    ( (λ u ux → yz u (xy u ux))
    , (λ u uz → yx u (zy u uz))
    )

  extensionality : ∀ x y → (∀ z → (z ∈ x) ↔ (z ∈ y)) → x ≈ y
  extensionality x y hyp =
    ( (λ z exz → _↔_.to (hyp z) exz)
    , (λ z eyz → _↔_.from (hyp z) eyz)
    )

  mem-ext : ∀ {x y} → x ≈ y → ∀ z → (z ∈ x) ↔ (z ∈ y)
  mem-ext {x} {y} (xy , yx) z = intro (xy z) (yx z)

  field
    ⟦_⟧     : Code → SetU
    by-decode≈ : ∀ {γ δ} → γ ≃K δ → ⟦ γ ⟧ ≈ ⟦ δ ⟧
    mem-congL : ∀ {x y} → x ≈ y → ∀ z → (x ∈ z) ↔ (y ∈ z)

    empty : Σ SetU (λ e → ∀ z → ¬ (z ∈ e))
    pairing : ∀ x y → Σ SetU (λ p → ∀ z → (z ∈ p) ↔ ((z ≈ x) ⊎ (z ≈ y)))
    union  : ∀ x → Σ SetU (λ u → ∀ z → (z ∈ u) ↔ (Σ SetU (λ y → (y ∈ x) × (z ∈ y))))
    powerset : ∀ x → Σ SetU (λ p → ∀ z → (z ∈ p) ↔ (∀ w → w ∈ z → w ∈ x))

    zeroS : SetU
    zeroS-empty : ∀ z → ¬ (z ∈ zeroS)
    succ  : SetU → SetU
    mem-succ↔ : ∀ x z → (z ∈ succ x) ↔ ((z ∈ x) ⊎ (z ≈ x))
    infinity : Σ SetU (λ ω → (∀ z → (z ∈ ω) ↔ ((z ≈ zeroS) ⊎ (Σ SetU (λ y → y ∈ ω × (z ≈ succ y))))))

    -- Formula semantics (one free variable, optionally with parameters encoded in the code).
    Pred : Code → SetU → Set ℓ
    Rel  : Code → SetU → SetU → Set ℓ

    -- Schemata over formulas/codes.
    separationᶠ
      : (φ : Code) → ∀ x →
        Σ SetU (λ y → ∀ z → (z ∈ y) ↔ ((z ∈ x) × (Pred φ z)))

  -- “Functional” means: the relation is single-valued (up to `≈`).
  FunctionalRel : (Rel : SetU → SetU → Set ℓ) → Set ℓ
  FunctionalRel Rel = ∀ u z₁ z₂ → Rel u z₁ → Rel u z₂ → z₁ ≈ z₂

  field
    -- Replacement applies when the coded binary relation is functional
    -- (single-valued, up to `≈`).
    replacementᶠ
      : (ψ : Code) → FunctionalRel (Rel ψ) → ∀ x →
        Σ SetU (λ y → ∀ z → (z ∈ y) ↔ (Σ SetU (λ u → (u ∈ x) × (Rel ψ u z))))

    foundation : ∀ x → (x ≈ zeroS) ⊎ (Σ SetU (λ y → y ∈ x × (∀ z → z ∈ x → ¬ (z ∈ y))))

record ZFCAxiomsᶠ {ℓ}
                 {Sig : LogOSSignature ℓ}
                 {Q   : QAdapter ℓ}
                 (K   : Kernel Sig Q)
                 : Set (lsuc (lsuc ℓ)) where
  field
    zf : ZFAxiomsᶠ K

  open ZFAxiomsᶠ zf public

  field
    AC : AC.AxiomOfChoice SetU _∈_ _≈_ pairing
