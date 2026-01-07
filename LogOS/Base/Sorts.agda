{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Base.Sorts where

-- ============================================================================
-- [Def 2.1] SORTS
-- The paper discusses a richer sort set; this module exposes the minimal subset
-- used by the implementation: interfaces and program cospans.
-- ============================================================================

open import LogOS.Prelude

record Sorts (ℓ : Level) : Set (lsuc ℓ) where
  field
    -- Interfaces and program carriers as primitives
    Iface : Set ℓ     -- Interface objects (boundary type)
    Cosp  : Set ℓ     -- Bulk programs (primitive carrier)
    ∂Cosp : Set ℓ     -- Boundary programs (primitive carrier)

open Sorts public
