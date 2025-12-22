{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Pack where

-- Canonical pack skeleton for the computational universality story.
-- Re-export the Assumptions/Claim/Pack/mkPack quartet from the theorem bundle,
-- plus small accessors to keep downstream code on the pack path.

open import LogOS.Prelude using (ℕ)

open import LogOS.Domain.UniversalIR.Theorems public
  using (Assumptions; Claim; Pack; mkPack; mkAssumptions)

open import LogOS.Domain.UniversalIR.Task using (PATask)
open import LogOS.Domain.UniversalIR.Schemes using
  ( minskyScheme
  ; lambdaScheme
  ; ethereumScheme
  ; oracleScheme
  ; quantumCircuitScheme
  )
import LogOS.Computation.Scheme as Sch

defaultAssumptions : Assumptions
defaultAssumptions = mkAssumptions

defaultPack : Pack defaultAssumptions
defaultPack = mkPack defaultAssumptions

claimOf : ∀ {A} → Pack A → Claim A
claimOf = Pack.claim

defaultClaim : Claim defaultAssumptions
defaultClaim = claimOf defaultPack

alg : ∀ {A} → Claim A → Sch.Algorithm PATask ℕ
alg = Claim.Alg

algOf : ∀ {A} → Pack A → Sch.Algorithm PATask ℕ
algOf p = alg (claimOf p)

minskyImplements
  : ∀ {A} (C : Claim A)
  → Sch.ImplementsRun (alg C) minskyScheme
minskyImplements C = Claim.minsky C

lambdaImplements
  : ∀ {A} (C : Claim A)
  → Sch.ImplementsRun (alg C) lambdaScheme
lambdaImplements C = Claim.lambda C

ethereumImplements
  : ∀ {A} (C : Claim A)
  → Sch.ImplementsRun (alg C) ethereumScheme
ethereumImplements C = Claim.ethereum C

oracleImplements
  : ∀ {A} (C : Claim A)
  → Sch.ImplementsRun (alg C) oracleScheme
oracleImplements C = Claim.oracle C

circuitImplements
  : ∀ {A} (C : Claim A)
  → Sch.ImplementsRun (alg C) quantumCircuitScheme
circuitImplements C = Claim.circuit C

minskyLambdaEq
  : ∀ {A} (C : Claim A)
  → Sch.RunEq minskyScheme lambdaScheme
minskyLambdaEq C = Claim.minsky≈lambda C

lambdaEthereumEq
  : ∀ {A} (C : Claim A)
  → Sch.RunEq lambdaScheme ethereumScheme
lambdaEthereumEq C = Claim.lambda≈ethereum C

minskyEthereumEq
  : ∀ {A} (C : Claim A)
  → Sch.RunEq minskyScheme ethereumScheme
minskyEthereumEq C =
  λ t →
    LogOS.Prelude.trans
      (minskyLambdaEq C t)
      (lambdaEthereumEq C t)

ethereumOracleEq
  : ∀ {A} (C : Claim A)
  → Sch.RunEq ethereumScheme oracleScheme
ethereumOracleEq C = Claim.ethereum≈oracle C

oracleCircuitEq
  : ∀ {A} (C : Claim A)
  → Sch.RunEq oracleScheme quantumCircuitScheme
oracleCircuitEq C = Claim.oracle≈circuit C
