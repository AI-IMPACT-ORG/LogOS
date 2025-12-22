{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Core.UCode where

open import LogOS.Prelude

open import LogOS.Domain.UniversalIR.Core.Ethereum using (EVMCode; stepE)
open import LogOS.Domain.UniversalIR.Core.Lambda using (LambdaCode; stepLC)
open import LogOS.Domain.UniversalIR.Core.Minsky using (MinskyCode; stepM)
open import LogOS.Domain.UniversalIR.Core.QuantumCircuit using (QuantumCircuitCode; stepQC)
open import LogOS.Domain.UniversalIR.Core.QuantumOracle using (QuantumCode; stepQ)

-- Unified IR carrier ---------------------------------------------------------

data UCode : Set where
  UM : MinskyCode → UCode
  UL : LambdaCode → UCode
  UE : EVMCode → UCode
  UQ : QuantumCode → UCode
  UQC : QuantumCircuitCode → UCode

stepU : UCode → UCode
stepU (UM m) = UM (stepM m)
stepU (UL l) = UL (stepLC l)
stepU (UE e) = UE (stepE e)
stepU (UQ q) = UQ (stepQ q)
stepU (UQC q) = UQC (stepQC q)

simulate : ℕ → UCode → UCode
simulate zero    u = u
simulate (suc n) u = simulate n (stepU u)
