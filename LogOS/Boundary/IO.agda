{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Boundary.IO where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.World
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Syntax.Prop as Prop
open import LogOS.Kernel.Core as Core

-- Swappable Boundary I/O interface.
--
-- This record packages the operational boundary (∂Cosp) as the primary
-- I/O view for the logic. It is parameterized by the existing world and
-- H-tier truth so it can be swapped without changing the core minimal
-- structures.

record BoundaryIO {ℓ : Level}
                  (Sig : LogOSSignature ℓ)
                  (Q   : QAdapter ℓ)
                  (W   : Worlds.WorldH Sig Q)
                  (BB  : BulkBoundary ℓ)
                  (H   : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB)
                  : Set (lsuc ℓ) where
  open LogOSSignature Sig
  module HT = Truth.HomotypicalTruth Sig Q W
  open BulkBoundary BB
  field
    -- Program-level boundary projections (I/O wiring).
    --
    -- These live at the level of contexts/programs. Do not confuse them with the
    -- constraint-level `ext`/`bnd` maps from `LaxAdjunction` (aka `Kernel.Holo`).
    to∂   : Cosp → ∂Cosp
    from∂ : ∂Cosp → Cosp

    -- Boundary satisfaction (I/O semantics) with S/H coherence
    Sat∂   : ∂Cosp → Con_bnd → Set ℓ
    sat-coh : ∀ (w : Cosp) (c : Con_bnd)
            → Prop._↔_ (HT.HLayer.Sat_H H w c)
                        (Sat∂ (to∂ w) c)

-- Canonical BoundaryIO derived from a kernel shape.
fromKernelShape
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (S : Core.KernelShape Sig Q)
  → BoundaryIO Sig Q (Core.KernelShape.HWorld S) (Core.KernelShape.BB S) (Core.KernelShape.HTruth S)
fromKernelShape {Sig = Sig} S =
  record
    { to∂    = to∂Sig
    ; from∂  = from∂Sig
    ; Sat∂   = Core.KernelShape.Sat_H_bnd S
    ; sat-coh = Core.KernelShape.sat-coh S
    }
  where
  open LogOSSignature Sig renaming (to∂ to to∂Sig; from∂ to from∂Sig)
