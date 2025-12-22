{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.PNTBridge where

open import LogOS.Prelude
open import Data.Product using (_×_; _,_)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Kernel
open import LogOS.Kernel.Endo

open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann using (RiemannSpectral)
open import LogOS.Domain.Opacity.TruthSeparation as TruthSep

-- PNT as stability: a model chooses a boundary constraint representing the
-- prime-counting asymptotic (in whatever semantics it prefers), proves that this
-- constraint is fixed by a local (finitely presented) closure, and then uses
-- separation (local ≃ Flow) to transport that stability to the global Flow.

record PNTFromGlobalTruthSeparation {ℓ}
                                   {Sig : LogOSSignature ℓ}
                                   {Q   : QAdapter ℓ}
                                   (K   : Kernel Sig Q)
                                   (RS  : RiemannSpectral)
                                   (Sep : TruthSep.GlobalTruthSeparation K RS)
                                   : Set (lsuc ℓ) where
  open Kernel K
  open TruthSep.GlobalTruthSeparation Sep
  CP = BulkBoundary.bnd BB

  field
    -- The PNT statement in the model’s chosen observer-facing semantics.
    PNT : Set ℓ

    -- Boundary constraint representing “PNT holds” (e.g., a constraint encoding
    -- an explicit-formula asymptotic, to be interpreted by a boundary semantics pack).
    pntC : ConPoset.Con CP

    -- Finite/constructive side: local closure already stabilizes pntC.
    pnt-local-fixed
      : ConPoset._⊑_ CP (Endo.fn local pntC) pntC
      × ConPoset._⊑_ CP pntC (Endo.fn local pntC)

    -- Interpretation step: global Flow stability at pntC implies the PNT statement.
    Flow-fixed→PNT
      : (ConPoset._⊑_ CP (Endo.fn (Flow-Endo K) pntC) pntC
       × ConPoset._⊑_ CP pntC (Endo.fn (Flow-Endo K) pntC))
      → PNT

  PNT-from-separation : PNT
  PNT-from-separation =
    Flow-fixed→PNT
      (TruthSep.local→Flow-fixed K local Flow≤local local≤Flow pntC pnt-local-fixed)

  -- Convenience: the same separation pack already yields guardless GRH at the boundary.
  GRH_Without_Vacuity_Guards
    : ∀ s → RiemannSpectral.NontrivialZero RS s → RiemannSpectral.OnLine RS s
  GRH_Without_Vacuity_Guards =
    TruthSep.GRH_Without_Vacuity_Guards_from_GlobalTruthSeparation K RS Sep
