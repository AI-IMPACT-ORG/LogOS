{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.UniversalIR.Core.UCode where

open import LogOS.Prelude

open import LogOS.UniversalIR.Core.Ethereum using (EVMCode; stepE)
open import LogOS.UniversalIR.Core.Lambda using (LambdaCode; stepLC)
open import LogOS.UniversalIR.Core.Minsky using (MinskyCode; stepM)
open import LogOS.UniversalIR.Core.QuantumCircuit using (QuantumCircuitCode; stepQC)
open import LogOS.UniversalIR.Core.QuantumOracle using (QuantumCode; stepQ)
open import LogOS.Computation.EvolutionOperator public using (EvolOperator)

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

-- Canonical evolution-operator instance for the unified IR.

EO-UCode : EvolOperator UCode stepU
EO-UCode = record
  { H = UCode
  ; embed = λ c → c
  ; Op = stepU
  ; intertwine = λ _ → refl
  }
