{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Semantic.Core where

-- Semantic “ports” = presentations of a shared boundary satisfaction relation.
--
-- This module provides the minimal interfaces; theorems live in
-- `LogOS.Ports.Semantic.HeteroInterlinguaCore` and `LogOS.Ports.Semantic.Interlingua`.

open import LogOS.Prelude

open import LogOS.Ports.Semantic.PresentationCore public using (SatSystem; satSystem)

open import LogOS.Base.Signature using (LogOSSignature; module LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary; module BulkBoundary)
open import LogOS.Minimal.World as Worlds
open import LogOS.Minimal.Truth as Truth
open import LogOS.Boundary.IO using (BoundaryIO; module BoundaryIO)

open import LogOS.Ports.Semantic.SatMor using (SatMor)
open import LogOS.Ports.Semantic.PresentationCore using (PresentationC; module PresentationC)

open import LogOS.Boundary.Port public
  using (BoundaryPort; canonicalPort)

open import LogOS.Ports.Semantic.HeteroInterlinguaCore public
  using (PresentationC; canonicalPresentation)

open import LogOS.Ports.Semantic.Interlingua public
  using (toPresentationC)

-- ---------------------------------------------------------------------------
-- SatSystem constructors (glue)
--
-- Note: “SatSystem” is the satisfaction triple (Ctx/Con/Sat), i.e. the common
-- currency of ports/presentations. It is *not* the boundary-first `LogOS.System.System`.
-- ---------------------------------------------------------------------------

-- Context-free systems (common when the “observer” is irrelevant / singleton).

CtxUnit : Set
CtxUnit = ⊤ {ℓ = lzero}

satSystem₀
  : ∀ {ℓCon ℓSat : Level}
    (Con : Set ℓCon)
    (Sat : CtxUnit → Con → Set ℓSat)
  → SatSystem {ℓCtx = lzero} {ℓCon = ℓCon} {ℓSat = ℓSat}
satSystem₀ Con Sat = satSystem CtxUnit Con Sat

-- Boundary-facing system at a signature boundary.

boundarySatSystem
  : ∀ {ℓ ℓSat : Level}
    {Sig : LogOSSignature ℓ}
    {BB : BulkBoundary ℓ}
  → (Sat∂ : LogOSSignature.∂Cosp Sig → BulkBoundary.Con_bnd BB → Set ℓSat)
  → SatSystem {ℓCtx = ℓ} {ℓCon = ℓ} {ℓSat = ℓSat}
boundarySatSystem {Sig = Sig} {BB = BB} Sat∂ =
  satSystem (LogOSSignature.∂Cosp Sig) (BulkBoundary.Con_bnd BB) Sat∂

boundarySatSystemFromIO
  : ∀ {ℓ : Level}
    {Sig : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q}
    {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  → BoundaryIO Sig Q W BB H
  → SatSystem {ℓCtx = ℓ} {ℓCon = ℓ} {ℓSat = ℓ}
boundarySatSystemFromIO {Sig = Sig} {BB = BB} B =
  boundarySatSystem {Sig = Sig} {BB = BB} (BoundaryIO.Sat∂ B)

-- Bulk-facing system of H-tier truth (same constraints, bulk contexts).

bulkSatSystemFromIO
  : ∀ {ℓ : Level}
    {Sig : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q}
    {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  → BoundaryIO Sig Q W BB H
  → SatSystem {ℓCtx = ℓ} {ℓCon = ℓ} {ℓSat = ℓ}
bulkSatSystemFromIO {Sig = Sig} {Q = Q} {W = W} {BB = BB} {H = H} _ =
  let
    module HT = Truth.HomotypicalTruth Sig Q W
  in
  satSystem (LogOSSignature.Cosp Sig) (BulkBoundary.Con_bnd BB) (HT.HLayer.Sat_H H)

-- The canonical bulk→boundary “communication” morphism provided by `BoundaryIO`.

bulkToBoundarySatMor
  : ∀ {ℓ : Level}
    {Sig : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q}
    {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    (B : BoundaryIO Sig Q W BB H)
  → SatMor (bulkSatSystemFromIO {Sig = Sig} {Q = Q} {W = W} {BB = BB} {H = H} B)
           (boundarySatSystemFromIO {Sig = Sig} {Q = Q} {W = W} {BB = BB} {H = H} B)
bulkToBoundarySatMor B =
  record
    { mapCtx = BoundaryIO.to∂ B
    ; mapCon = λ c → c
    ; sat-↔  = BoundaryIO.sat-coh B
    }

-- Presentations are systems too: they expose their own formula language.

presentationSatSystem
  : ∀ {ℓCtx ℓCon ℓSat ℓForm : Level}
    {S : SatSystem {ℓCtx = ℓCtx} {ℓCon = ℓCon} {ℓSat = ℓSat}}
  → PresentationC {ℓForm = ℓForm} S
  → SatSystem {ℓCtx = ℓCtx} {ℓCon = ℓForm} {ℓSat = ℓSat}
presentationSatSystem {S = S} P =
  let
    module Sₛ = SatSystem S
    module Pₛ = PresentationC P
  in
  satSystem Sₛ.Ctx Pₛ.Form Pₛ.SatF

-- More literature-aligned alias names (kept lightweight).

BoundaryPresentation = BoundaryPort
Presentation = PresentationC
