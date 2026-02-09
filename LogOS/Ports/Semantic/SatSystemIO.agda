{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Semantic.SatSystemIO where

-- A tiny “external logic system I/O” wrapper:
-- a presentation (syntax+semantics) together with prover/solver interfaces.
--
-- This is designed to make interoperability *operational*: once a single
-- prover/solver exists for one presentation, LogOS can rebase it to any other
-- presentation (and, along `SatMor`, across changing logics) by construction.

open import LogOS.Prelude
open import LogOS.Syntax.ProofSystem

open import LogOS.Ports.Semantic.HeteroInterlinguaCore using (PresentationC)
open import LogOS.Ports.Semantic.SatMor using (SatMor)
open import LogOS.Ports.Semantic.PresentationCore using (SatSystem)
import LogOS.Ports.Semantic.ProofTransport as PT

-- Note: this module’s “System” is a `SatSystem` (Ctx/Con/Sat), not an open
-- `LogOS.System.System`.

-- ---------------------------------------------------------------------------
-- Tool I/O over a single satisfaction relation.
-- ---------------------------------------------------------------------------

record SatSystemIO
  {ℓName ℓCtx ℓCon ℓSat ℓForm ℓWProver ℓWModel : Level}
  (Name : Set ℓName)
  (S : SatSystem {ℓCtx = ℓCtx} {ℓCon = ℓCon} {ℓSat = ℓSat})
  : Set (lsuc (lsuc (ℓName ⊔ ℓCtx ⊔ ℓCon ⊔ ℓSat ⊔ ℓForm ⊔ ℓWProver ⊔ ℓWModel))) where

  field
    name : Name
    Pres : PresentationC {ℓForm = ℓForm} S

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
    {S : SatSystem {ℓCtx = ℓCtx} {ℓCon = ℓCon} {ℓSat = ℓSat}}
    (P₁ : PresentationC {ℓForm = ℓForm₁} S)
  → SatSystemIO {ℓForm = ℓForm₂} {ℓWProver = ℓWProver} {ℓWModel = ℓWModel} Name S
  → SatSystemIO {ℓForm = ℓForm₁} {ℓWProver = ℓWProver} {ℓWModel = ℓWModel} Name S
rebase P₁ sys =
  let
    open SatSystemIO sys renaming (Pres to P₂)
    module PB = PT.Shared P₁ P₂
  in
  record
    { name         = name
    ; Pres         = P₁
    ; Prover       = PB.pullbackProver Prover
    ; ModelChecker = PB.pullbackModelChecker ModelChecker
    }

rebase-prover-complete
  : ∀ {ℓName ℓCtx ℓCon ℓSat ℓForm₁ ℓForm₂ ℓWProver ℓWModel}
    {Name : Set ℓName}
    {S : SatSystem {ℓCtx = ℓCtx} {ℓCon = ℓCon} {ℓSat = ℓSat}}
    (P₁ : PresentationC {ℓForm = ℓForm₁} S)
    (sys : SatSystemIO {ℓForm = ℓForm₂} {ℓWProver = ℓWProver} {ℓWModel = ℓWModel} Name S)
  → Complete (SatSystemIO.Prover sys)
  → Complete (SatSystemIO.Prover (rebase P₁ sys))
rebase-prover-complete P₁ sys comp =
  let
    open SatSystemIO sys renaming (Pres to P₂)
    module PB = PT.Shared P₁ P₂
  in
  PB.pullbackProver-complete comp

rebase-modelChecker-complete
  : ∀ {ℓName ℓCtx ℓCon ℓSat ℓForm₁ ℓForm₂ ℓWProver ℓWModel}
    {Name : Set ℓName}
    {S : SatSystem {ℓCtx = ℓCtx} {ℓCon = ℓCon} {ℓSat = ℓSat}}
    (P₁ : PresentationC {ℓForm = ℓForm₁} S)
    (sys : SatSystemIO {ℓForm = ℓForm₂} {ℓWProver = ℓWProver} {ℓWModel = ℓWModel} Name S)
  → Complete (SatSystemIO.ModelChecker sys)
  → Complete (SatSystemIO.ModelChecker (rebase P₁ sys))
rebase-modelChecker-complete P₁ sys comp =
  let
    open SatSystemIO sys renaming (Pres to P₂)
    module PB = PT.Shared P₁ P₂
  in
  PB.pullbackModelChecker-complete comp

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

record SatSystemIO↑
  {ℓName ℓCtx ℓCon ℓSat ℓForm ℓLift ℓWProver ℓWModel : Level}
  (Name : Set ℓName)
  (S : SatSystem {ℓCtx = ℓCtx} {ℓCon = ℓCon} {ℓSat = ℓSat})
  : Set (lsuc (lsuc (ℓName ⊔ ℓCtx ⊔ ℓCon ⊔ ℓSat ⊔ ℓForm ⊔ ℓLift ⊔ ℓWProver ⊔ ℓWModel))) where

  field
    name : Name
    Pres : PresentationC {ℓForm = ℓForm} S

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
    {S₁ : SatSystem {ℓCtx = ℓCtx₁} {ℓCon = ℓCon₁} {ℓSat = ℓSat₁}}
    {S₂ : SatSystem {ℓCtx = ℓCtx₂} {ℓCon = ℓCon₂} {ℓSat = ℓSat₂}}
    (m  : SatMor S₁ S₂)
    (P₁ : PresentationC {ℓForm = ℓForm₁} S₁)
  → SatSystemIO {ℓForm = ℓForm₂} {ℓWProver = ℓWProver} {ℓWModel = ℓWModel} Name S₂
  → SatSystemIO↑ {ℓForm = ℓForm₁} {ℓLift = ℓCtx₂ ⊔ ℓSat₂} {ℓWProver = ℓWProver} {ℓWModel = ℓWModel} Name S₁
rebaseAlongSatMor m P₁ sys =
  let
    open SatSystemIO sys renaming (Pres to P₂)
    module PB = PT.AlongSatMor m P₁ P₂
  in
  record
    { name         = name
    ; Pres         = P₁
    ; Prover       = PB.pullbackProverFromGlobal Prover
    ; ModelChecker = PB.pullbackModelCheckerFromGlobal ModelChecker
    }
