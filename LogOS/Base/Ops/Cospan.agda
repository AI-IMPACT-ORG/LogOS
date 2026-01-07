{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Base.Ops.Cospan where

-- ============================================================================
-- [Def 2.4] STRUCTURED COSPAN OPERATIONS
-- Function symbols for bulk programs (structured cospans)
-- ============================================================================

open import LogOS.Prelude

-- Recommended laws (documentation-only):
-- - Source/target coherence:
--     src (idC A) ≡ A, tgt (idC A) ≡ A
--     src (g ∘C f) ≡ src f, tgt (g ∘C f) ≡ tgt g
-- - Composition (_∘C_) is associative and unital (idC is left/right identity).
-- - Overlay/tensor (_⊕C_, _⊗C_) satisfy monoid-like laws in your model
--   (assoc/unit; commutativity if intended), and preserve interfaces in the
--   expected way (e.g., src (f ⊗C g) determined by src f, src g).

record CospanOps {ℓ : Level} (Cosp Iface : Set ℓ) : Set ℓ where
  field
    -- Interface projections (primitive)
    src   : Cosp → Iface      -- Source interface
    tgt   : Cosp → Iface      -- Target interface

    -- Primitive program operations (no categorical requirements)
    idC   : Iface → Cosp      -- Identity program for an interface
    _∘C_  : Cosp → Cosp → Cosp   -- Sequential composition
    _⊕C_  : Cosp → Cosp → Cosp   -- Overlay/choice
    _⊗C_  : Cosp → Cosp → Cosp   -- Tensor/wiring

  infixr 9 _∘C_
  infixl 6 _⊕C_
  infixl 7 _⊗C_

open CospanOps public
