{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.Indistinguishability where

-- Indistinguishability as observational equivalence, with adapters as simulators.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; ↔-sym; ↔-trans)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.World as Worlds
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth
open import LogOS.Boundary.IO using (BoundaryIO)
open import LogOS.Boundary.Port using (BoundaryPort)
open import LogOS.Ports.Semantic.PresentationCore using (PresentationC)

import LogOS.Ports.Semantic.Interoperability as Interop
import LogOS.Ports.Semantic.Interlingua as Interlingua

IndistinguishableF
  : ∀ {ℓ ℓForm}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q}
    {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    {B : BoundaryIO Sig Q W BB H}
  → (P : BoundaryPort {ℓForm = ℓForm} Sig Q W BB H B)
  → BoundaryPort.Form P → BoundaryPort.Form P → Set ℓ
IndistinguishableF P φ ψ = ∀ p → BoundaryPort.SatF P p φ ↔ BoundaryPort.SatF P p ψ

simulator-preserves
  : ∀ {ℓ ℓForm₁ ℓForm₂}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q}
    {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    {B : BoundaryIO Sig Q W BB H}
    {P₁ : BoundaryPort {ℓForm = ℓForm₁} Sig Q W BB H B}
    {P₂ : BoundaryPort {ℓForm = ℓForm₂} Sig Q W BB H B}
  → (A : Interop.PortAdapter B P₁ P₂)
  → ∀ {φ ψ}
  → IndistinguishableF P₁ φ ψ
  → IndistinguishableF P₂ (Interop.PortAdapter.map A φ) (Interop.PortAdapter.map A ψ)
simulator-preserves A eq p =
  let stepφ = Interop.PortAdapter.preserves-Sat A p _
      stepψ = Interop.PortAdapter.preserves-Sat A p _
  in
  ↔-trans (↔-sym stepφ) (↔-trans (eq p) stepψ)

simulator-preserves-ObsEqF
  : ∀ {ℓ ℓForm₁ ℓForm₂}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q}
    {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    {B : BoundaryIO Sig Q W BB H}
    {P₁ : BoundaryPort {ℓForm = ℓForm₁} Sig Q W BB H B}
    {P₂ : BoundaryPort {ℓForm = ℓForm₂} Sig Q W BB H B}
  → (A : Interop.PortAdapter B P₁ P₂)
  → ∀ {φ ψ}
  → PresentationC.ObsEqF (Interlingua.toPresentationC B P₁) φ ψ
  → PresentationC.ObsEqF (Interlingua.toPresentationC B P₂)
      (Interop.PortAdapter.map A φ)
      (Interop.PortAdapter.map A ψ)
simulator-preserves-ObsEqF A =
  Interop.adapter-respects-ObsEqF _ A
