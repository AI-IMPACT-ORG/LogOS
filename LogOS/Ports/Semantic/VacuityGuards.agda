{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Semantic.VacuityGuards where

-- Vacuity guards for ports/adapters: guard against trivial satisfaction and
-- constant adapters that erase boundary distinctions.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import LogOS.Base.Signature using (LogOSSignature; module LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.World
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Boundary.IO
open import LogOS.Boundary.Port
open import LogOS.Ports.Semantic.Interoperability using (PortAdapter)

record PortVacuityGuards
  {ℓ : Level}
  {ℓForm : Level}
  {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  {W : Worlds.WorldH Sig Q}
  {BB : BulkBoundary ℓ}
  {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  (B : BoundaryIO Sig Q W BB H)
  (P : BoundaryPort {ℓForm = ℓForm} Sig Q W BB H B)
  : Set (lsuc (ℓ ⊔ ℓForm)) where
  open LogOSSignature Sig
  open BoundaryIO B
  open BoundaryPort P
  field
    p : ∂Cosp
    φ₀ φ₁ : Form
    sat₀ : SatF p φ₀
    unsat₁ : ¬ (SatF p φ₁)
    import-distinct : ¬ (Import φ₀ ≡ Import φ₁)

record AdapterVacuityGuards
  {ℓ : Level}
  {ℓForm₁ ℓForm₂ : Level}
  {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  {W : Worlds.WorldH Sig Q}
  {BB : BulkBoundary ℓ}
  {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  (B : BoundaryIO Sig Q W BB H)
  (P₁ : BoundaryPort {ℓForm = ℓForm₁} Sig Q W BB H B)
  (P₂ : BoundaryPort {ℓForm = ℓForm₂} Sig Q W BB H B)
  (A : PortAdapter B P₁ P₂)
  : Set (lsuc (ℓ ⊔ ℓForm₁ ⊔ ℓForm₂)) where
  open LogOSSignature Sig
  private
    module P1 = BoundaryPort P₁
  open PortAdapter A
  field
    p : ∂Cosp
    φ₀ φ₁ : P1.Form
    sat₀ : P1.SatF p φ₀
    unsat₁ : ¬ (P1.SatF p φ₁)
    φ₀≢φ₁ : ¬ (φ₀ ≡ φ₁)
    map-distinct : ¬ (map φ₀ ≡ map φ₁)
