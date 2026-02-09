{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Semantic.BoundarySystemIO where

-- Convenience constructors for “external logic system I/O” at the boundary-port level.
--
-- This is just glue:
-- - turn a `BoundaryPort` into a `PresentationC` (via `toPresentationC`)
-- - build a `SatSystemIO` (presentation + prover + model-checker)
-- - rebase an existing `SatSystemIO` to another boundary port

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
open import LogOS.Ports.Semantic.Core using (boundarySatSystemFromIO)
open import LogOS.Ports.Semantic.SatSystemIO using (SatSystemIO; SatSystemIO↑; rebase; rebaseAlongSatMor)
import LogOS.Ports.Semantic.Interoperability as Interop
open import LogOS.System using (System)

-- Build a `SatSystemIO` directly from a boundary port and tool interfaces.

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
  → let S = boundarySatSystemFromIO B
    in SatSystemIO
        {ℓForm = ℓForm}
        {ℓWProver = ℓWProver}
        {ℓWModel = ℓWModel}
        Name S
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
  → let S = boundarySatSystemFromIO B
    in SatSystemIO
        {ℓForm = ℓForm₂}
        {ℓWProver = ℓWProver}
        {ℓWModel = ℓWModel}
        Name S
    → SatSystemIO
        {ℓForm = ℓForm₁}
        {ℓWProver = ℓWProver}
        {ℓWModel = ℓWModel}
        Name S
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
  → let S = boundarySatSystemFromIO B
    in SatSystemIO
        {ℓForm = ℓForm₂}
        {ℓWProver = ℓWProver}
        {ℓWModel = ℓWModel}
        Name S
    → SatSystemIO
        {ℓForm = ℓForm₁}
        {ℓWProver = ℓWProver}
        {ℓWModel = ℓWModel}
        Name S
-- NOTE: the adapter argument is intentionally unused: rebasing is defined via
-- the forced/canonical translation between presentations (interlingua), and by
-- adapter confluence any two adapters between the same ports agree up to
-- satisfaction (↔). We accept an adapter here mainly to help type inference at
-- call sites (it pins down `P₁`/`P₂`).
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
      (boundarySatSystemFromIO B₁)
      (boundarySatSystemFromIO B₂)
  → let S₂ = boundarySatSystemFromIO B₂
        S₁ = boundarySatSystemFromIO B₁
    in SatSystemIO
        {ℓForm = ℓForm₂}
        {ℓWProver = ℓWProver}
        {ℓWModel = ℓWModel}
        Name S₂
    → SatSystemIO↑
        {ℓForm = ℓForm₁}
        {ℓWProver = ℓWProver}
        {ℓWModel = ℓWModel}
        Name S₁
rebaseAlongSatMorToBoundaryPort B₁ P₁ m sys =
  rebaseAlongSatMor m (toPresentationC B₁ P₁) sys

-- ---------------------------------------------------------------------------
-- System-first wrappers
--
-- These keep the underlying currency the same (boundary satisfaction systems),
-- but let downstream code quantify over `LogOS.System.System` rather than over
-- bare `BoundaryIO`.
-- ---------------------------------------------------------------------------

module ForSystem
  {ℓName ℓ ℓForm₁ ℓForm₂ ℓWProver ℓWModel : Level}
  {Name : Set ℓName}
  (S : System {ℓ = ℓ})
  where

  open System S

  systemIOFromBoundaryPortS
    : (P : BoundaryPort {ℓForm = ℓForm₁} Sig Q W BB H B)
    → (name : Name)
    → ProofSystem
        {ℓI = ℓForm₁}
        {ℓP = ℓ}
        {ℓW = ℓWProver}
        (BoundaryPort.Form P)
        (λ φ → ∀ p → BoundaryPort.SatF P p φ)
    → ProofSystem
        {ℓI = ℓ ⊔ ℓForm₁}
        {ℓP = ℓ}
        {ℓW = ℓWModel}
        (LogOSSignature.∂Cosp Sig × BoundaryPort.Form P)
        (λ where (p , φ) → BoundaryPort.SatF P p φ)
    → SatSystemIO
        {ℓForm = ℓForm₁}
        {ℓWProver = ℓWProver}
        {ℓWModel = ℓWModel}
        Name boundarySatSystem
  systemIOFromBoundaryPortS P name Prover ModelChecker =
    systemIOFromBoundaryPort B P name Prover ModelChecker

  rebaseToBoundaryPortS
    : (P₁ : BoundaryPort {ℓForm = ℓForm₁} Sig Q W BB H B)
    → SatSystemIO
        {ℓForm = ℓForm₂}
        {ℓWProver = ℓWProver}
        {ℓWModel = ℓWModel}
        Name boundarySatSystem
    → SatSystemIO
        {ℓForm = ℓForm₁}
        {ℓWProver = ℓWProver}
        {ℓWModel = ℓWModel}
        Name boundarySatSystem
  rebaseToBoundaryPortS P₁ sys =
    rebaseToBoundaryPort B P₁ sys

  rebaseViaPortAdapterS
    : {P₁ : BoundaryPort {ℓForm = ℓForm₁} Sig Q W BB H B}
    → {P₂ : BoundaryPort {ℓForm = ℓForm₂} Sig Q W BB H B}
    → Interop.PortAdapter B P₁ P₂
    → SatSystemIO
        {ℓForm = ℓForm₂}
        {ℓWProver = ℓWProver}
        {ℓWModel = ℓWModel}
        Name boundarySatSystem
    → SatSystemIO
        {ℓForm = ℓForm₁}
        {ℓWProver = ℓWProver}
        {ℓWModel = ℓWModel}
        Name boundarySatSystem
  rebaseViaPortAdapterS A sys =
    rebaseViaPortAdapter B A sys

  rebaseAlongSatMorToBoundaryPortS
    : (P₁ : BoundaryPort {ℓForm = ℓForm₁} Sig Q W BB H B)
    → ∀ {Sig₂ : LogOSSignature ℓ} {Q₂ : QAdapter ℓ}
      {W₂ : Worlds.WorldH Sig₂ Q₂}
      {BB₂ : BulkBoundary ℓ}
      {H₂ : (let module HT₂ = Truth.HomotypicalTruth Sig₂ Q₂ W₂ in HT₂.HLayer) BB₂}
      {B₂ : BoundaryIO Sig₂ Q₂ W₂ BB₂ H₂}
    → SatMor (boundarySatSystemFromIO B) (boundarySatSystemFromIO B₂)
    → SatSystemIO
        {ℓForm = ℓForm₂}
        {ℓWProver = ℓWProver}
        {ℓWModel = ℓWModel}
        Name (boundarySatSystemFromIO B₂)
    → SatSystemIO↑
        {ℓForm = ℓForm₁}
        {ℓWProver = ℓWProver}
        {ℓWModel = ℓWModel}
        Name (boundarySatSystemFromIO B)
  rebaseAlongSatMorToBoundaryPortS P₁ {B₂ = B₂} m sys =
    rebaseAlongSatMorToBoundaryPort B P₁ {B₂ = B₂} m sys
