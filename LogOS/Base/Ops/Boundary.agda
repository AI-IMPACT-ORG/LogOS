{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Base.Ops.Boundary where

-- ============================================================================
-- [Def 2.5] BOUNDARY OPERATIONS
-- Function symbols for boundary programs and bulk-boundary maps
-- ============================================================================

open import LogOS.Prelude

-- Recommended laws (documentation-only):
-- - Source/target coherence:
--     src∂ (id∂ A) ≡ A, tgt∂ (id∂ A) ≡ A
--     src∂ (g ∘∂ f) ≡ src∂ f, tgt∂ (g ∘∂ f) ≡ tgt∂ g
-- - Composition (_∘∂_) is associative and unital (id∂ is left/right identity).
-- - Bulk/boundary coherence via ext/bnd is captured as a lax adjunction at
--   the constraint level (see Minimal.Adjunction for the unit/counit laws).
-- - _⊕∂_, _⊗∂_ mirror their bulk counterparts when present in your model.

record BoundaryOps {ℓ : Level} (∂Cosp Iface Cosp : Set ℓ) : Set ℓ where
  field
    -- Interface projections (primitive)
    src∂ : ∂Cosp → Iface
    tgt∂ : ∂Cosp → Iface
    
    -- Boundary operations (primitive, parallel to bulk)
    id∂   : Iface → ∂Cosp
    _∘∂_  : ∂Cosp → ∂Cosp → ∂Cosp
    _⊕∂_  : ∂Cosp → ∂Cosp → ∂Cosp
    _⊗∂_  : ∂Cosp → ∂Cosp → ∂Cosp
    
    -- Bulk-boundary maps (lax adjunction captured elsewhere)
    from∂ : ∂Cosp → Cosp
    to∂   : Cosp → ∂Cosp

  infixr 9 _∘∂_
  infixl 6 _⊕∂_
  infixl 7 _⊗∂_

open BoundaryOps public
