{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.Guards.Ports where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature; module LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.World as Worlds
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth
open import LogOS.Boundary.IO using (BoundaryIO)
open import LogOS.Boundary.Port using (BoundaryPort)
open import LogOS.Ports.Semantic.Interoperability using (PortAdapter)

open import LogOS.Theorems.Meta.Guards
open import LogOS.Ports.Semantic.VacuityGuards as Vac

-- Port/adaptor vacuity guards imply nontriviality of satisfaction at some boundary
-- point (at the chosen witness `p`).

nonVacuousSatF
  : ∀ {ℓ : Level}
    {ℓForm : Level}
    {Sig : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q}
    {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    {B : BoundaryIO Sig Q W BB H}
    {P : BoundaryPort {ℓForm = ℓForm} Sig Q W BB H B}
  → Vac.PortVacuityGuards B P
  → NonVacuousSat
      (LogOSSignature.∂Cosp Sig)
      (BoundaryPort.Form P)
      (BoundaryPort.SatF P)
nonVacuousSatF G =
  let open Vac.PortVacuityGuards G renaming (sat₀ to satF₀; unsat₁ to unsatF₁) in
  record
    { w = p
    ; c₀ = φ₀
    ; c₁ = φ₁
    ; sat₀ = satF₀
    ; unsat₁ = unsatF₁
    }

nontrivialSatF
  : ∀ {ℓ : Level}
    {ℓForm : Level}
    {Sig : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q}
    {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    {B : BoundaryIO Sig Q W BB H}
    {P : BoundaryPort {ℓForm = ℓForm} Sig Q W BB H B}
  → Vac.PortVacuityGuards B P
  → Σ (LogOSSignature.∂Cosp Sig)
      (λ p → NontrivialPred (BoundaryPort.Form P)
                            (BoundaryPort.SatF P p))
nontrivialSatF G =
  let NV = nonVacuousSatF G in
  NonVacuousSat.w NV , NonVacuousSat.at NV

nonVacuousSatF-adapter
  : ∀ {ℓ : Level}
    {ℓForm₁ ℓForm₂ : Level}
    {Sig : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q}
    {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    {B : BoundaryIO Sig Q W BB H}
    {P₁ : BoundaryPort {ℓForm = ℓForm₁} Sig Q W BB H B}
    {P₂ : BoundaryPort {ℓForm = ℓForm₂} Sig Q W BB H B}
    {A : PortAdapter B P₁ P₂}
  → Vac.AdapterVacuityGuards B P₁ P₂ A
  → NonVacuousSat
      (LogOSSignature.∂Cosp Sig)
      (BoundaryPort.Form P₁)
      (BoundaryPort.SatF P₁)
nonVacuousSatF-adapter G =
  let open Vac.AdapterVacuityGuards G renaming (sat₀ to satF₀; unsat₁ to unsatF₁) in
  record
    { w = p
    ; c₀ = φ₀
    ; c₁ = φ₁
    ; sat₀ = satF₀
    ; unsat₁ = unsatF₁
    }

nontrivialSatF-adapter
  : ∀ {ℓ : Level}
    {ℓForm₁ ℓForm₂ : Level}
    {Sig : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q}
    {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    {B : BoundaryIO Sig Q W BB H}
    {P₁ : BoundaryPort {ℓForm = ℓForm₁} Sig Q W BB H B}
    {P₂ : BoundaryPort {ℓForm = ℓForm₂} Sig Q W BB H B}
    {A : PortAdapter B P₁ P₂}
  → Vac.AdapterVacuityGuards B P₁ P₂ A
  → Σ (LogOSSignature.∂Cosp Sig)
      (λ p → NontrivialPred (BoundaryPort.Form P₁)
                            (BoundaryPort.SatF P₁ p))
nontrivialSatF-adapter G =
  let NV = nonVacuousSatF-adapter G in
  NonVacuousSat.w NV , NonVacuousSat.at NV
