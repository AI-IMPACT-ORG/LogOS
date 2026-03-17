{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.SetTheory.MembershipLaws where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; intro)

-- Membership-derived relations and their basic laws.
--
-- This module intentionally stays minimal and `--safe`: it is reused by both the
-- set-theory axiom packs and the ZF transformer stack context.
module Laws {ℓ : Level} {SetU : Set ℓ} (_∈_ : SetU → SetU → Set ℓ) where
  infix 4 _⊆_ _≈_

  _⊆_ : SetU → SetU → Set ℓ
  x ⊆ y = ∀ z → (z ∈ x) → (z ∈ y)

  _≈_ : SetU → SetU → Set ℓ
  x ≈ y = (x ⊆ y) × (y ⊆ x)

  refl≈ : ∀ x → x ≈ x
  refl≈ _ = (λ _ zx → zx) , (λ _ zy → zy)

  sym≈ : ∀ {x y} → x ≈ y → y ≈ x
  sym≈ xy = snd xy , fst xy

  trans≈ : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
  trans≈ xy yz =
    ( (λ u ux → fst yz u (fst xy u ux))
    , (λ u uz → snd xy u (snd yz u uz))
    )

  -- “Presentation layer” (↔) implies extensional equality.
  extensionality : ∀ x y → (∀ z → (z ∈ x) ↔ (z ∈ y)) → x ≈ y
  extensionality x y hyp =
    ( (λ z exz → _↔_.to (hyp z) exz)
    , (λ z eyz → _↔_.from (hyp z) eyz)
    )

  -- Extensional equality yields pointwise membership equivalence.
  mem-ext : ∀ {x y} → x ≈ y → ∀ z → (z ∈ x) ↔ (z ∈ y)
  mem-ext xy z = intro (fst xy z) (snd xy z)

  -- Propositional equality implies extensional equality.
  ≡→≈ : ∀ {x y} → x ≡ y → x ≈ y
  ≡→≈ {x} eq = subst (λ t → x ≈ t) eq (refl≈ x)
