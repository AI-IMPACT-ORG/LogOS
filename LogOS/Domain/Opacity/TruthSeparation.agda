{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.TruthSeparation where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Kernel
open import LogOS.Kernel.Endo
open import LogOS.Theorems.Meta.GRHBridge as GRHB

open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann

-- Shared helper: cast a Riemann spectral pack into the nucleus-friendly record.

RStoSP : RiemannSpectral → GRHB.SpectralPack lzero
RStoSP RS = record
  { Spectral       = RiemannSpectral.Spectral RS
  ; OnLine         = RiemannSpectral.OnLine RS
  ; NontrivialZero = RiemannSpectral.NontrivialZero RS
  }

-- General “global vs local truth” assumption record.
-- A local endomap (candidate truth closure) is sandwiched between Flow-Endo,
-- and its fixed points track spectral witnesses via c.

record GlobalTruthSeparation {ℓ}
                              {Sig : LogOSSignature ℓ}
                              {Q   : QAdapter ℓ}
                              (K   : Kernel Sig Q)
                              (RS  : RiemannSpectral)
                              : Set (lsuc (ℓ ⊔ lzero)) where
  open Kernel K
  open RiemannSpectral RS
  field
    local     : Endo K
    Flow≤local  : _≤₂_ K (Flow-Endo K) local
    local≤Flow  : _≤₂_ K local (Flow-Endo K)

    c : Spectral → ConPoset.Con (BulkBoundary.bnd BB)

    zero→local-fixed
      : ∀ s → NontrivialZero s →
        ConPoset._⊑_ (BulkBoundary.bnd BB) (Endo.fn local (c s)) (c s)
        × ConPoset._⊑_ (BulkBoundary.bnd BB) (c s) (Endo.fn local (c s))

    local-fixed→OnLine
      : ∀ s →
        (ConPoset._⊑_ (BulkBoundary.bnd BB) (Endo.fn local (c s)) (c s)
       × ConPoset._⊑_ (BulkBoundary.bnd BB) (c s) (Endo.fn local (c s)))
        → OnLine s

-- Transport local fixedness (sandwiched by Flow-Endo) to Flow fixedness.

local→Flow-fixed
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (local : Endo K)
    (Flow≤local : _≤₂_ K (Flow-Endo K) local)
    (local≤Flow : _≤₂_ K local (Flow-Endo K))
    (c : ConPoset.Con (BulkBoundary.bnd (Kernel.BB K)))
    → (ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K)) (Endo.fn local c) c
      × ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K)) c (Endo.fn local c))
    → (ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K)) (Endo.fn (Flow-Endo K) c) c
      × ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K)) c (Endo.fn (Flow-Endo K) c))
local→Flow-fixed K local Flow≤local local≤Flow c (lc≤c , c≤lc) =
  let open Kernel K
      CP = BulkBoundary.bnd BB
      Flowc≤localc = Flow≤local c
      localc≤Flowc = local≤Flow c
      Flowc≤c = ConPoset.trans CP Flowc≤localc lc≤c
      c≤Flowc = ConPoset.trans CP c≤lc localc≤Flowc
  in Flowc≤c , c≤Flowc

Flow→local-fixed
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (local : Endo K)
    (Flow≤local : _≤₂_ K (Flow-Endo K) local)
    (local≤Flow : _≤₂_ K local (Flow-Endo K))
    (c : ConPoset.Con (BulkBoundary.bnd (Kernel.BB K)))
    → (ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K)) (Endo.fn (Flow-Endo K) c) c
      × ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K)) c (Endo.fn (Flow-Endo K) c))
    → (ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K)) (Endo.fn local c) c
      × ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K)) c (Endo.fn local c))
Flow→local-fixed K local Flow≤local local≤Flow c (Flowc≤c , c≤Flowc) =
  let open Kernel K
      CP = BulkBoundary.bnd BB
      localc≤Flowc = local≤Flow c
      Flowc≤localc = Flow≤local c
      localc≤c = ConPoset.trans CP localc≤Flowc Flowc≤c
      c≤localc = ConPoset.trans CP c≤Flowc Flowc≤localc
  in localc≤c , c≤localc

-- | Build the nucleus bridge that transports the local closure `local` across
-- the Flow projector. This is the canonical “logic Langlands” square entry.
globalNucleusBridge
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (RS : RiemannSpectral)
    (Sep : GlobalTruthSeparation {ℓ} {Sig} {Q} K RS)
  → GRHB.GlobalNucleusBridge K (RStoSP RS)
globalNucleusBridge K RS Sep =
  let open GlobalTruthSeparation Sep
      zero→Flow s nz =
        local→Flow-fixed K local Flow≤local local≤Flow (c s) (zero→local-fixed s nz)
      PFixed→OnLine s flowFixed =
        local-fixed→OnLine s
          (Flow→local-fixed K local Flow≤local local≤Flow (c s) flowFixed)
  in record
       { Pr = GRHB.FlowProjector K
       ; c  = c
       ; zero→PFixed = zero→Flow
       ; PFixed→OnLine = PFixed→OnLine
       }

-- Main theorem: sandwiched closures coincide with Flow fixed points, forcing
-- GRH_Without_Vacuity_Guards.

GRH_Without_Vacuity_Guards_from_GlobalTruthSeparation
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K    : Kernel Sig Q)
    (RS   : RiemannSpectral)
    (Sep  : GlobalTruthSeparation {ℓ} {Sig} {Q} K RS)
  → ∀ s → RiemannSpectral.NontrivialZero RS s → RiemannSpectral.OnLine RS s
GRH_Without_Vacuity_Guards_from_GlobalTruthSeparation K RS Sep =
  GRHB.GRH_Without_Vacuity_Guards_via_GlobalNucleus K (RStoSP RS) (globalNucleusBridge K RS Sep)
