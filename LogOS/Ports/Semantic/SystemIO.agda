{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Semantic.SystemIO where

-- A tiny “external logic system I/O” wrapper:
-- a presentation (syntax+semantics) together with prover/solver interfaces.
--
-- This is designed to make interoperability *operational*: once a single
-- prover/solver exists for one presentation, LogOS can rebase it to any other
-- presentation (and, along `SatMor`, across changing logics) by construction.

open import LogOS.Prelude
open import LogOS.Syntax.ProofSystem

open import LogOS.Ports.Semantic.InterlinguaCore using (PresentationC)
open import LogOS.Ports.Semantic.SatMor using (SatMor)
import LogOS.Ports.Semantic.ProofTransport as PT

-- ---------------------------------------------------------------------------
-- System I/O over a single satisfaction relation.
-- ---------------------------------------------------------------------------

record SystemIO
  {ℓName ℓCtx ℓCon ℓSat ℓForm ℓWProver ℓWModel : Level}
  (Name : Set ℓName)
  (Ctx  : Set ℓCtx)
  (Con  : Set ℓCon)
  (SatC : Ctx → Con → Set ℓSat)
  : Set (lsuc (lsuc (ℓName ⊔ ℓCtx ⊔ ℓCon ⊔ ℓSat ⊔ ℓForm ⊔ ℓWProver ⊔ ℓWModel))) where

  field
    name : Name
    Pres : PresentationC {ℓForm = ℓForm} Ctx Con SatC

  open PresentationC Pres public

  -- “Input/output tasks” for external tools.
  Valid : Form → Set (ℓCtx ⊔ ℓSat)
  Valid φ = ∀ p → SatF p φ

  Sat : Ctx × Form → Set ℓSat
  Sat x = SatF (x .fst) (x .snd)

  field
    Prover      : ProofSystem {ℓI = ℓForm} {ℓP = ℓCtx ⊔ ℓSat} {ℓW = ℓWProver} Form Valid
    ModelChecker : ProofSystem {ℓI = ℓCtx ⊔ ℓForm} {ℓP = ℓSat} {ℓW = ℓWModel} (Ctx × Form) Sat

-- Rebase a system to a different presentation over the same satisfaction.
-- This is the “one-liner”: it reuses the original system’s proofs/certificates.

rebase
  : ∀ {ℓName ℓCtx ℓCon ℓSat ℓForm₁ ℓForm₂ ℓWProver ℓWModel}
    {Name : Set ℓName}
    {Ctx  : Set ℓCtx}
    {Con  : Set ℓCon}
    {SatC : Ctx → Con → Set ℓSat}
    (P₁ : PresentationC {ℓForm = ℓForm₁} Ctx Con SatC)
  → SystemIO {ℓForm = ℓForm₂} {ℓWProver = ℓWProver} {ℓWModel = ℓWModel} Name Ctx Con SatC
  → SystemIO {ℓForm = ℓForm₁} {ℓWProver = ℓWProver} {ℓWModel = ℓWModel} Name Ctx Con SatC
rebase P₁ sys =
  let
    open SystemIO sys renaming (Pres to P₂)
    module PB = PT.Shared P₁ P₂
  in
  record
    { name         = name
    ; Pres         = P₁
    ; Prover       = PB.pullbackProver Prover
    ; ModelChecker = PB.pullbackModelChecker ModelChecker
    }

-- ---------------------------------------------------------------------------
-- Rebase along a satisfaction morphism.
-- ---------------------------------------------------------------------------

-- Note: for a general `SatMor`, transporting *global validity* (`∀ p → ...`) is
-- not canonical *covariantly* (it would require additional hypotheses about
-- `mapCtx`, e.g. surjectivity). What is canonical is the *pullback* direction:
-- tools for the target system can be rebased to the source system.
--
-- In particular, context-indexed satisfiability/model-checking transports
-- directly via `mapCtx`, and a target prover for global validity can always be
-- pulled back to a prover for the source logic.

record SystemIO↑
  {ℓName ℓCtx ℓCon ℓSat ℓForm ℓLift ℓWProver ℓWModel : Level}
  (Name : Set ℓName)
  (Ctx  : Set ℓCtx)
  (Con  : Set ℓCon)
  (SatC : Ctx → Con → Set ℓSat)
  : Set (lsuc (lsuc (ℓName ⊔ ℓCtx ⊔ ℓCon ⊔ ℓSat ⊔ ℓForm ⊔ ℓLift ⊔ ℓWProver ⊔ ℓWModel))) where

  field
    name : Name
    Pres : PresentationC {ℓForm = ℓForm} Ctx Con SatC

  open PresentationC Pres public

  Valid : Form → Set (ℓCtx ⊔ ℓSat)
  Valid φ = ∀ p → SatF p φ

  Valid↑ : Form → Set ((ℓCtx ⊔ ℓSat) ⊔ ℓLift)
  Valid↑ φ = Lift ℓLift (Valid φ)

  Sat↑ : Ctx × Form → Set (ℓSat ⊔ ℓLift)
  Sat↑ x = Lift ℓLift (SatF (x .fst) (x .snd))

  field
    Prover : ProofSystem {ℓI = ℓForm} {ℓP = (ℓCtx ⊔ ℓSat) ⊔ ℓLift} {ℓW = ℓWProver} Form Valid↑
    ModelChecker : ProofSystem {ℓI = ℓCtx ⊔ ℓForm} {ℓP = ℓSat ⊔ ℓLift} {ℓW = ℓWModel} (Ctx × Form) Sat↑

rebaseAlongSatMor
  : ∀ {ℓName ℓCtx₁ ℓCon₁ ℓSat₁ ℓForm₁ ℓCtx₂ ℓCon₂ ℓSat₂ ℓForm₂ ℓWProver ℓWModel}
    {Name : Set ℓName}
    {Ctx₁ : Set ℓCtx₁} {Con₁ : Set ℓCon₁} {Sat₁ : Ctx₁ → Con₁ → Set ℓSat₁}
    {Ctx₂ : Set ℓCtx₂} {Con₂ : Set ℓCon₂} {Sat₂ : Ctx₂ → Con₂ → Set ℓSat₂}
    (m  : SatMor Ctx₁ Con₁ Sat₁ Ctx₂ Con₂ Sat₂)
    (P₁ : PresentationC {ℓForm = ℓForm₁} Ctx₁ Con₁ Sat₁)
  → SystemIO {ℓForm = ℓForm₂} {ℓWProver = ℓWProver} {ℓWModel = ℓWModel} Name Ctx₂ Con₂ Sat₂
  → SystemIO↑ {ℓForm = ℓForm₁} {ℓLift = ℓCtx₂ ⊔ ℓSat₂} {ℓWProver = ℓWProver} {ℓWModel = ℓWModel} Name Ctx₁ Con₁ Sat₁
rebaseAlongSatMor
  {ℓCtx₁ = ℓCtx₁} {ℓSat₁ = ℓSat₁} {ℓCtx₂ = ℓCtx₂} {ℓSat₂ = ℓSat₂} {ℓForm₂ = ℓForm₂} {ℓWProver = ℓWProver} {ℓWModel = ℓWModel}
  {Ctx₁ = Ctx₁} {Ctx₂ = Ctx₂}
  m P₁ sys =
  let
    open SystemIO sys renaming (Pres to P₂)
    module PB = PT.AlongSatMor m P₁ P₂
  in
  record
    { name         = name
    ; Pres         = P₁
    ; Prover       = PB.pullbackProverFromGlobal Prover
    ; ModelChecker = PB.pullbackModelCheckerFromGlobal ModelChecker
    }
