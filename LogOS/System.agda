{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.System where

-- Boundary-first “open system” interface:
-- a packaged BoundaryIO together with its ambient signature/world/truth data.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature; module LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary; module BulkBoundary)
open import LogOS.Minimal.World as Worlds
open import LogOS.Minimal.Truth as Truth
open import LogOS.Boundary.IO using (BoundaryIO; module BoundaryIO)
open import LogOS.Boundary.Port using (BoundaryPort; canonicalPort)

open import LogOS.Ports.Semantic.PresentationCore using (SatSystem)
open import LogOS.Ports.Semantic.Core using (boundarySatSystemFromIO)
open import LogOS.Ports.Semantic.HeteroInterlinguaCore using (PresentationC; canonicalPresentation)

record System {ℓ : Level} : Set (lsuc (lsuc ℓ)) where
  field
    Sig : LogOSSignature ℓ
    Q   : QAdapter ℓ

    W   : Worlds.WorldH Sig Q
    BB  : BulkBoundary ℓ
    H   : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB

    B   : BoundaryIO Sig Q W BB H

  -- Re-export the “open system” primitives:
  -- - the signature types (Cosp/∂Cosp etc.), but *not* its default `to∂/from∂`
  --   wiring (those are supplied by `B`).
  open LogOSSignature Sig public hiding (to∂; from∂)
  open BulkBoundary BB public
  open BoundaryIO B public

  -- Canonical bridge: every open system induces a satisfaction system at its boundary.
  --
  -- This is the `Ctx/Con/Sat` triple used pervasively by the ports/adapters spine.
  boundarySatSystem : SatSystem {ℓCtx = ℓ} {ℓCon = ℓ} {ℓSat = ℓ}
  boundarySatSystem = boundarySatSystemFromIO B

  -- Canonical boundary port/presentation derived from the open system.

  boundaryPort∂ : BoundaryPort {ℓForm = ℓ} Sig Q W BB H B
  boundaryPort∂ = canonicalPort B

  boundaryPresentation : PresentationC boundarySatSystem
  boundaryPresentation = canonicalPresentation boundarySatSystem

-- Bridge: any boundary I/O induces an open boundary-first `System`.
fromBoundaryIO
  : ∀ {ℓ : Level}
    {Sig : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q}
    {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  → BoundaryIO Sig Q W BB H
  → System {ℓ = ℓ}
fromBoundaryIO {Sig = Sig} {Q = Q} {W = W} {BB = BB} {H = H} B =
  record
    { Sig = Sig
    ; Q = Q
    ; W = W
    ; BB = BB
    ; H = H
    ; B = B
    }
