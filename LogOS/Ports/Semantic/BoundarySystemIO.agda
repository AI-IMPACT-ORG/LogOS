{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Semantic.BoundarySystemIO where

-- Convenience constructors for “external logic system I/O” at the boundary-port level.
--
-- This is just glue:
-- - turn a `BoundaryPort` into a `PresentationC` (via `toPresentationC`)
-- - build a `SystemIO` (presentation + prover + model-checker)
-- - rebase an existing `SystemIO` to another boundary port

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.World
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Boundary.IO using (BoundaryIO)
open import LogOS.Boundary.Port using (BoundaryPort)

open import LogOS.Syntax.ProofSystem using (ProofSystem)

open import LogOS.Ports.Semantic.Interlingua using (toPresentationC)
open import LogOS.Ports.Semantic.SatMor using (SatMor)
open import LogOS.Ports.Semantic.SystemIO using (SystemIO; SystemIO↑; rebase; rebaseAlongSatMor)
import LogOS.Ports.Semantic.Interoperability as Interop

-- Build a `SystemIO` directly from a boundary port and tool interfaces.

systemIOFromBoundaryPort
  : ∀ {ℓName ℓ ℓForm ℓWProver ℓWModel}
    {Name : Set ℓName}
    {Sig : LogOSSignature ℓ}
    {Q   : QAdapter ℓ}
    {W   : Worlds.WorldH Sig Q}
    {BB  : BulkBoundary ℓ}
    {H   : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    (B   : BoundaryIO Sig Q W BB H)
    (P   : BoundaryPort {ℓForm = ℓForm} Sig Q W BB H B)
  → (name : Name)
  → ProofSystem
      {ℓI = ℓForm}
      {ℓP = ℓ}
      {ℓW = ℓWProver}
      (BoundaryPort.Form P)
      (λ φ → ∀ p → BoundaryPort.SatF P p φ)
  → ProofSystem
      {ℓI = ℓ ⊔ ℓForm}
      {ℓP = ℓ}
      {ℓW = ℓWModel}
      (LogOSSignature.∂Cosp Sig × BoundaryPort.Form P)
      (λ where (p , φ) → BoundaryPort.SatF P p φ)
  → SystemIO
      {ℓForm = ℓForm}
      {ℓWProver = ℓWProver}
      {ℓWModel = ℓWModel}
      Name (LogOSSignature.∂Cosp Sig) (BulkBoundary.Con_bnd BB) (BoundaryIO.Sat∂ B)
systemIOFromBoundaryPort B P name Prover ModelChecker =
  record
    { name         = name
    ; Pres         = toPresentationC B P
    ; Prover       = Prover
    ; ModelChecker = ModelChecker
    }

-- Rebase any boundary-satisfaction system I/O to a chosen boundary port.

rebaseToBoundaryPort
  : ∀ {ℓName ℓ ℓForm₁ ℓForm₂ ℓWProver ℓWModel}
    {Name : Set ℓName}
    {Sig : LogOSSignature ℓ}
    {Q   : QAdapter ℓ}
    {W   : Worlds.WorldH Sig Q}
    {BB  : BulkBoundary ℓ}
    {H   : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    (B   : BoundaryIO Sig Q W BB H)
    (P₁  : BoundaryPort {ℓForm = ℓForm₁} Sig Q W BB H B)
  → SystemIO
      {ℓForm = ℓForm₂}
      {ℓWProver = ℓWProver}
      {ℓWModel = ℓWModel}
      Name (LogOSSignature.∂Cosp Sig) (BulkBoundary.Con_bnd BB) (BoundaryIO.Sat∂ B)
  → SystemIO
      {ℓForm = ℓForm₁}
      {ℓWProver = ℓWProver}
      {ℓWModel = ℓWModel}
      Name (LogOSSignature.∂Cosp Sig) (BulkBoundary.Con_bnd BB) (BoundaryIO.Sat∂ B)
rebaseToBoundaryPort B P₁ sys = rebase (toPresentationC B P₁) sys

rebaseViaPortAdapter
  : ∀ {ℓName ℓ ℓForm₁ ℓForm₂ ℓWProver ℓWModel}
    {Name : Set ℓName}
    {Sig : LogOSSignature ℓ}
    {Q   : QAdapter ℓ}
    {W   : Worlds.WorldH Sig Q}
    {BB  : BulkBoundary ℓ}
    {H   : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    (B   : BoundaryIO Sig Q W BB H)
    {P₁  : BoundaryPort {ℓForm = ℓForm₁} Sig Q W BB H B}
    {P₂  : BoundaryPort {ℓForm = ℓForm₂} Sig Q W BB H B}
  → Interop.PortAdapter B P₁ P₂
  → SystemIO
      {ℓForm = ℓForm₂}
      {ℓWProver = ℓWProver}
      {ℓWModel = ℓWModel}
      Name (LogOSSignature.∂Cosp Sig) (BulkBoundary.Con_bnd BB) (BoundaryIO.Sat∂ B)
  → SystemIO
      {ℓForm = ℓForm₁}
      {ℓWProver = ℓWProver}
      {ℓWModel = ℓWModel}
      Name (LogOSSignature.∂Cosp Sig) (BulkBoundary.Con_bnd BB) (BoundaryIO.Sat∂ B)
rebaseViaPortAdapter B {P₁ = P₁} _ sys = rebase (toPresentationC B P₁) sys

rebaseAlongSatMorToBoundaryPort
  : ∀ {ℓName ℓ ℓForm₁ ℓForm₂ ℓWProver ℓWModel}
    {Name : Set ℓName}
    {Sig₁ Sig₂ : LogOSSignature ℓ}
    {Q₁ Q₂ : QAdapter ℓ}
    {W₁ : Worlds.WorldH Sig₁ Q₁}
    {W₂ : Worlds.WorldH Sig₂ Q₂}
    {BB₁ BB₂ : BulkBoundary ℓ}
    {H₁ : (let module HT = Truth.HomotypicalTruth Sig₁ Q₁ W₁ in HT.HLayer) BB₁}
    {H₂ : (let module HT = Truth.HomotypicalTruth Sig₂ Q₂ W₂ in HT.HLayer) BB₂}
    (B₁ : BoundaryIO Sig₁ Q₁ W₁ BB₁ H₁)
    (P₁ : BoundaryPort {ℓForm = ℓForm₁} Sig₁ Q₁ W₁ BB₁ H₁ B₁)
    {B₂ : BoundaryIO Sig₂ Q₂ W₂ BB₂ H₂}
  → SatMor
      (LogOSSignature.∂Cosp Sig₁)
      (BulkBoundary.Con_bnd BB₁)
      (BoundaryIO.Sat∂ B₁)
      (LogOSSignature.∂Cosp Sig₂)
      (BulkBoundary.Con_bnd BB₂)
      (BoundaryIO.Sat∂ B₂)
  → SystemIO
      {ℓForm = ℓForm₂}
      {ℓWProver = ℓWProver}
      {ℓWModel = ℓWModel}
      Name (LogOSSignature.∂Cosp Sig₂) (BulkBoundary.Con_bnd BB₂) (BoundaryIO.Sat∂ B₂)
  → SystemIO↑
      {ℓForm = ℓForm₁}
      {ℓWProver = ℓWProver}
      {ℓWModel = ℓWModel}
      Name (LogOSSignature.∂Cosp Sig₁) (BulkBoundary.Con_bnd BB₁) (BoundaryIO.Sat∂ B₁)
rebaseAlongSatMorToBoundaryPort B₁ P₁ m sys =
  rebaseAlongSatMor m (toPresentationC B₁ P₁) sys
