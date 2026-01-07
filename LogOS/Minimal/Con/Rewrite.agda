{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Minimal.Con.Rewrite where

-- Small proof toolkit: rewrite endpoints of a refinement (`_⊑_`) along equality.
--
-- This is used to keep “transport-heavy” proofs stable and readable without
-- adding any new axioms.

open import LogOS.Prelude

open import LogOS.Minimal.Con

module For {ℓ : Level} (CP : ConPoset ℓ) where
  open ConPoset CP

  -- Rewrite the left endpoint.
  substL : ∀ {a a' b} → a ≡ a' → _⊑_ a b → _⊑_ a' b
  substL {b = b} eq le = subst (λ x → _⊑_ x b) eq le

  -- Rewrite the right endpoint.
  substR : ∀ {a b b'} → b ≡ b' → _⊑_ a b → _⊑_ a b'
  substR {a = a} eq le = subst (λ x → _⊑_ a x) eq le

  -- Rewrite both endpoints.
  substLR : ∀ {a a' b b'} → a ≡ a' → b ≡ b' → _⊑_ a b → _⊑_ a' b'
  substLR eqL eqR le = substR eqR (substL eqL le)
