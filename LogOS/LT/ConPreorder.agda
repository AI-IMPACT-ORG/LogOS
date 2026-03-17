{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.ConPreorder where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- `ConPreorder` is the LT-layer name for the canonical refinement kit.
--
-- Canonical definition lives in `LogOS.Prelude.Refinement` (so all refinement
-- structure is defined once, below LT).

open import LogOS.Prelude

-- Anchor for claim-stamps: keep a stable `≡→≈` name in this module even though
-- the canonical definition lives below LT.
open LogOS.Prelude.RefinementKit public renaming (Refinement to ConPreorder)

trans⊑
  : ∀ {ℓCon ℓRel} (CP : ConPreorder ℓCon ℓRel) {a b c : Con CP}
  → _⊑_ CP a b → _⊑_ CP b c → _⊑_ CP a c
trans⊑ CP = ConPreorder.trans CP

≈-trans
  : ∀ {ℓCon ℓRel} {CP : ConPreorder ℓCon ℓRel} {a b c : Con CP}
  → _≈_ CP a b → _≈_ CP b c → _≈_ CP a c
≈-trans {CP = CP} (ab , ba) (bc , cb) =
  (trans⊑ CP ab bc , trans⊑ CP cb ba)

-- “Sandwich” refinement through a shared middle point.
--
-- If two constraints are observationally equivalent to the same middle constraint,
-- then they are equivalent at the pullback level; this makes this lemma the
-- mutual refinement variant of the “shared-middle” idiom.
sandwich⊑
  : ∀ {ℓCon ℓRel} {CP : ConPreorder ℓCon ℓRel} {a b m : Con CP}
  → _≈_ CP a m
  → _≈_ CP b m
  → _⊑_ CP a b
sandwich⊑ {CP = CP} (a≤m , _) (_ , m≤b) =
  trans⊑ CP a≤m m≤b

-- Mutual refinement via a shared middle point.
--
-- This is the symmetric version of `sandwich⊑` when the same `≈` hypotheses are
-- available in both directions.
sandwich≈
  : ∀ {ℓCon ℓRel} {CP : ConPreorder ℓCon ℓRel} {a b m : Con CP}
  → _≈_ CP a m
  → _≈_ CP b m
  → _≈_ CP a b
sandwich≈ {CP = CP} {a = a} {b = b} {m = m} abm bm =
  ( sandwich⊑ {CP = CP} {a = a} {b = b} {m = m} abm bm
  , sandwich⊑ {CP = CP} {a = b} {b = a} {m = m} bm abm
  )

Reflects⊑
  : ∀ {ℓCon₁ ℓRel₁ ℓCon₂ ℓRel₂}
  → (CP₁ : ConPreorder ℓCon₁ ℓRel₁)
  → (CP₂ : ConPreorder ℓCon₂ ℓRel₂)
  → (Con CP₁ → Con CP₂)
  → Set (ℓCon₁ ⊔ ℓRel₁ ⊔ ℓRel₂)
Reflects⊑ CP₁ CP₂ f =
  ∀ {a b}
  → _⊑_ CP₂ (f a) (f b)
  → _⊑_ CP₁ a b

Reflects≈
  : ∀ {ℓCon₁ ℓRel₁ ℓCon₂ ℓRel₂}
  → (CP₁ : ConPreorder ℓCon₁ ℓRel₁)
  → (CP₂ : ConPreorder ℓCon₂ ℓRel₂)
  → (Con CP₁ → Con CP₂)
  → Set (ℓCon₁ ⊔ ℓRel₁ ⊔ ℓRel₂)
Reflects≈ CP₁ CP₂ f =
  ∀ {a b}
  → _≈_ CP₂ (f a) (f b)
  → _≈_ CP₁ a b
