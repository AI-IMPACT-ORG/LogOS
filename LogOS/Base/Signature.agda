{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Base.Signature where

-- ============================================================================
-- L_LogOS SIGNATURE
-- The complete signature bundling all sorts, operations, and relations
-- ============================================================================

open import LogOS.Prelude

-- Import minimal components (without opening field accessors)
import LogOS.Base.Sorts as S
import LogOS.Base.Ops.Cospan as Cosp
import LogOS.Base.Ops.Boundary as Bnd

-- ============================================================================
-- COMPLETE LogOS SIGNATURE
-- ============================================================================

record LogOSSignature (ℓ : Level) : Set (lsuc ℓ) where
  field
    -- Minimal sorts: keep the existing definition for compatibility
    sorts : S.Sorts ℓ

  open S.Sorts sorts public

  field
    -- Minimal program and boundary operations only (no categorical structure)
    cospanOps   : Cosp.CospanOps Cosp Iface
    boundaryOps : Bnd.BoundaryOps ∂Cosp Iface Cosp

  -- Re-export only the minimal operations
  open Cosp.CospanOps cospanOps public
  open Bnd.BoundaryOps boundaryOps public
