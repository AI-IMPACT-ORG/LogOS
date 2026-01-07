{-
LogOS: an Agda research library for foundational logic system architecture.
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
open import LogOS.Ports.Semantic.SystemIO using (SystemIO; rebase)

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
