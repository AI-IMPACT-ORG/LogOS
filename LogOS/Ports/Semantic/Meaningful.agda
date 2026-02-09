{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Semantic.Meaningful where

-- First-class non-triviality witnesses for satisfaction systems / boundary I/O.
--
-- These records are intentionally small:
-- - they provide concrete satisfying + refuting witnesses,
-- - they imply both definitional and observational distinguishability,
-- - they are stable inputs for “anti-vacuity” theorems and tooling layers.

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop using (¬_)

open import LogOS.Ports.Semantic.PresentationCore using (SatSystem)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.World as Worlds
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Boundary.IO using (BoundaryIO)
open import LogOS.Boundary.Port using (_≈∂[_]_; BoundaryPort; canonicalPort)

import LogOS.Ports.Semantic.VacuityGuards as Vac

record MeaningfulSatSystem
  {ℓCtx ℓCon ℓSat : Level}
  (S : SatSystem {ℓCtx = ℓCtx} {ℓCon = ℓCon} {ℓSat = ℓSat})
  : Set (ℓCtx ⊔ ℓCon ⊔ ℓSat) where
  open SatSystem S renaming (Sat to SatC)
  field
    p     : Ctx
    c₀ c₁ : Con
    sat₀  : SatC p c₀
    unsat₁ : ¬ (SatC p c₁)

  -- Derived: representational distinctness.
  c₀≢c₁ : ¬ (c₀ ≡ c₁)
  c₀≢c₁ eq = unsat₁ (subst (SatC p) eq sat₀)

  -- Derived: observational distinctness.
  obsDistinct : ¬ (ObsEq c₀ c₁)
  obsDistinct eq = unsat₁ (Prop.to (eq p) sat₀)

  -- Derived: mutual-refinement distinctness (canonical `≈`-shaped form).
  obsDistinct≈ : ¬ (Obs≈ c₀ c₁)
  obsDistinct≈ (c₀≤c₁ , _) = unsat₁ (c₀≤c₁ p sat₀)

record MeaningfulBoundaryIO
  {ℓ : Level}
  {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
  {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  (B : BoundaryIO Sig Q W BB H)
  : Set (ℓ ⊔ ℓ) where
  open LogOSSignature Sig using (∂Cosp)
  open BulkBoundary BB using (Con_bnd)
  open BoundaryIO B using (Sat∂)
  field
    p     : ∂Cosp
    c₀ c₁ : Con_bnd
    sat₀  : Sat∂ p c₀
    unsat₁ : ¬ (Sat∂ p c₁)

  -- Derived: representational distinctness.
  c₀≢c₁ : ¬ (c₀ ≡ c₁)
  c₀≢c₁ eq = unsat₁ (subst (Sat∂ p) eq sat₀)

  -- Derived: observational distinctness (w.r.t. boundary satisfaction).
  obsDistinct : ¬ (c₀ ≈∂[ B ] c₁)
  obsDistinct eq = unsat₁ (fst eq p sat₀)

-- ---------------------------------------------------------------------------
-- Conversions to existing vacuity guards (ports/adapters spine).
-- ---------------------------------------------------------------------------

meaningfulBoundaryIO→canonicalPortGuards
  : ∀ {ℓ : Level}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    (B : BoundaryIO Sig Q W BB H)
  → MeaningfulBoundaryIO B
  → Vac.PortVacuityGuards B (canonicalPort B)
meaningfulBoundaryIO→canonicalPortGuards B M =
  record
    { p = MeaningfulBoundaryIO.p M
    ; φ₀ = MeaningfulBoundaryIO.c₀ M
    ; φ₁ = MeaningfulBoundaryIO.c₁ M
    ; sat₀ = MeaningfulBoundaryIO.sat₀ M
    ; unsat₁ = MeaningfulBoundaryIO.unsat₁ M
    }

portGuards→meaningfulBoundaryIO
  : ∀ {ℓ : Level}
    {ℓForm : Level}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    {B : BoundaryIO Sig Q W BB H}
    (P : BoundaryPort {ℓForm = ℓForm} Sig Q W BB H B)
  → Vac.PortVacuityGuards B P
  → MeaningfulBoundaryIO B
portGuards→meaningfulBoundaryIO {B = B} P G =
  let
    module P0 = BoundaryPort P
    open Vac.PortVacuityGuards G
    sat₀∂ = Prop.to (P0.SatF≈∂ p φ₀) sat₀
    unsat₁∂ : ¬ (BoundaryIO.Sat∂ B p (P0.Import φ₁))
    unsat₁∂ sat = unsat₁ (Prop.from (P0.SatF≈∂ p φ₁) sat)
  in
  record
    { p = p
    ; c₀ = P0.Import φ₀
    ; c₁ = P0.Import φ₁
    ; sat₀ = sat₀∂
    ; unsat₁ = unsat₁∂
    }
