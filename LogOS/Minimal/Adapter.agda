{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Minimal.Adapter where

open import Level using (Level; lsuc)

-- Quantale + Time adapter as a single parameter
-- Keeps only the minimal structure needed by the Minimal core
-- Recommended (but not enforced) structure:
-- - (Scale, _·_, e) forms a monoid:
--     associativity: (a · b) · c ≡ a · (b · c)
--     left/right unit: e · a ≡ a and a · e ≡ a
-- - Order compatibility: _≤s_ is a preorder and is monotone in both arguments w.r.t. _·_
-- - Time forms a monoid (_+_, zero) with τ : Time → Scale a monoid morphism:
--     τ (t + s) ≡ τ t · τ s and τ zero ≡ e
-- - Optional proof/derivability order _≤p_ can coincide with _≤s_

record QAdapter (ℓ : Level) : Set (lsuc ℓ) where
  infix 4 _≤s_ _≤p_
  infixl 6 _+_
  infixl 7 _·_
  field
    -- Scale (quantale-like carrier)
    Scale   : Set ℓ
    _≤s_    : Scale → Scale → Set ℓ
    _·_     : Scale → Scale → Scale
    e       : Scale

    -- Optional proof/derivability order (can coincide with _≤s_)
    _≤p_    : Scale → Scale → Set ℓ

    -- Time monoid and embedding into Scale
    Time    : Set ℓ
    _+_     : Time → Time → Time
    zero    : Time
    τ       : Time → Scale
