{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.GRHBridge where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel
-- GRH meta-bridges phrased without any operator or analytic imports.
-- This module keeps the core agnostic and provides only the categorical
-- (projector/nucleus) closure shape needed for conditional GRH wrappers.

open import LogOS.Minimal.Con
open import LogOS.Theorems.Projective as Proj
open import LogOS.Minimal.Truth as Truth
open import LogOS.Ports.SpectralPack public using (SpectralPack)

-- Categorical deformation: nucleus/closure (projector) bridge
-- Provide a projector P on the boundary poset and show that nontrivial zeros
-- pick P-fixed boundary constraints via a selector c; assume a meta clause that
-- any such P-fixed witness entails OnLine. This avoids mentioning operators and
-- matches standard closure/nucleus axioms.

record GlobalNucleusBridge {ℓ ℓS}
                           {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                           (K   : Kernel Sig Q)
                           (RS  : SpectralPack ℓS)
                           : Set (lsuc (ℓ ⊔ ℓS)) where
  open Kernel K
  open SpectralPack RS
  open ConPoset (BulkBoundary.bnd BB)
  field
    Pr : Proj.Projector (BulkBoundary.bnd BB)
    c  : Spectral → Con
    -- Nontrivial zeros produce P-fixed witnesses at c s (two inequalities)
    zero→PFixed : ∀ s → NontrivialZero s →
      ConPoset._⊑_ (BulkBoundary.bnd BB) (Proj.Projector.P Pr (c s)) (c s)
      × ConPoset._⊑_ (BulkBoundary.bnd BB) (c s) (Proj.Projector.P Pr (c s))
    -- A meta clause: any such P-fixed witness forces OnLine
    PFixed→OnLine : ∀ s →
      (ConPoset._⊑_ (BulkBoundary.bnd BB) (Proj.Projector.P Pr (c s)) (c s)
     × ConPoset._⊑_ (BulkBoundary.bnd BB) (c s) (Proj.Projector.P Pr (c s)))
      → OnLine s

GRH_Without_Vacuity_Guards_via_GlobalNucleus
  : ∀ {ℓ ℓS} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K   : Kernel Sig Q)
    (RS  : SpectralPack ℓS)
    (GN  : GlobalNucleusBridge K RS)
  → ∀ s → SpectralPack.NontrivialZero RS s → SpectralPack.OnLine RS s
GRH_Without_Vacuity_Guards_via_GlobalNucleus K RS GN s nz =
  let open GlobalNucleusBridge GN in
  PFixed→OnLine s (zero→PFixed s nz)

-- Limit (finite→infinite) nucleus bridge
-- A general, operator‑free continuity principle phrased with projectors.

record GlobalNucleusLimit {ℓ ℓS}
                          {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                          (K   : Kernel Sig Q)
    (RS  : SpectralPack ℓS)
    (Idx : Set)
                          : Set (lsuc (ℓ ⊔ ℓS)) where
  open Kernel K
  open SpectralPack RS
  field
    -- Finite projectors and a limit projector on the boundary poset
    Prᵢ : Idx → Proj.Projector (BulkBoundary.bnd BB)
    Pr∞ : Proj.Projector (BulkBoundary.bnd BB)

    -- Spectral selector into boundary constraints
    c   : Spectral → ConPoset.Con (BulkBoundary.bnd BB)

    -- Finite witnesses: every nontrivial zero yields Prᵢ‑fixed at c s (both inequalities)
    zero→PᵢFixed : ∀ i s → NontrivialZero s →
      ConPoset._⊑_ (BulkBoundary.bnd BB) (Proj.Projector.P (Prᵢ i) (c s)) (c s)
      × ConPoset._⊑_ (BulkBoundary.bnd BB) (c s) (Proj.Projector.P (Prᵢ i) (c s))

    -- Continuity/limit clause: from all finite fixedness obtain limit fixedness
    all→limFixed : ∀ s →
      (∀ i → ConPoset._⊑_ (BulkBoundary.bnd BB) (Proj.Projector.P (Prᵢ i) (c s)) (c s)
            × ConPoset._⊑_ (BulkBoundary.bnd BB) (c s) (Proj.Projector.P (Prᵢ i) (c s)))
      → ConPoset._⊑_ (BulkBoundary.bnd BB) (Proj.Projector.P Pr∞ (c s)) (c s)
      × ConPoset._⊑_ (BulkBoundary.bnd BB) (c s) (Proj.Projector.P Pr∞ (c s))

    -- Spectral clause at the limit: Pr∞‑fixed implies OnLine
    P∞Fixed→OnLine : ∀ s →
      (ConPoset._⊑_ (BulkBoundary.bnd BB) (Proj.Projector.P Pr∞ (c s)) (c s)
     × ConPoset._⊑_ (BulkBoundary.bnd BB) (c s) (Proj.Projector.P Pr∞ (c s)))
      → OnLine s

GRH_Without_Vacuity_Guards_via_GlobalNucleus∞
  : ∀ {ℓ ℓS} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K   : Kernel Sig Q)
    (RS  : SpectralPack ℓS)
    {Idx : Set}
    (GL  : GlobalNucleusLimit K RS Idx)
  → ∀ s → SpectralPack.NontrivialZero RS s → SpectralPack.OnLine RS s
GRH_Without_Vacuity_Guards_via_GlobalNucleus∞ K RS {Idx} GL s nz =
  let open GlobalNucleusLimit GL in
  let allFixed
        : ∀ i →
          ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K)) (Proj.Projector.P (Prᵢ i) (c s)) (c s)
          × ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K)) (c s) (Proj.Projector.P (Prᵢ i) (c s))
      allFixed i = zero→PᵢFixed i s nz in
  P∞Fixed→OnLine s (all→limFixed s allFixed)

-- The "very natural" nucleus in this logic: the global Flow projector on the boundary.
-- Build a GlobalNucleusBridge from a finite operator bridge by transporting Op-fixed
-- to Flow-fixed (hence P-fixed) via HPFlow, and reusing OpFixed→OnLine.

FlowProjector
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → Proj.Projector (BulkBoundary.bnd (Kernel.BB K))
FlowProjector {Sig = Sig} {Q = Q} K =
  let module FG0 = Proj.ForG {Sig = Sig} {Q = Q} in
  FG0.fromGuarded {CP = BulkBoundary.bnd (Kernel.BB K)} (Kernel.GTruth K)
