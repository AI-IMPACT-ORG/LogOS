{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Universality.NatBoundary where

-- Canonical Nat boundary for universality base layers (refinement-first).
--
-- This module exists to avoid the “refinement collapse” pattern `_⊑_ = _≡_`
-- in base layers that are meant to model *resource monotonicity*.
--
-- Reading:
-- - boundary elements are “available budget/fuel” amounts,
-- - refinement is ordinary ≤ (more budget/fuel is stronger, it entails less).

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder)
open import LogOS.Prelude.Nat.Order using (_≤ℕ_; z≤n; s≤s; ≤ℕ-refl; ≤ℕ-trans)

NatBoundary : ConPreorder lzero lzero
NatBoundary =
  record
    { Con   = ℕ
    ; _⊑_   = _≤ℕ_
    ; refl  = ≤ℕ-refl
    ; trans = ≤ℕ-trans
    }
