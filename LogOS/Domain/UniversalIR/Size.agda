{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Size where

open import LogOS.Prelude

open import LogOS.Domain.UniversalIR.Task as Task using (PATask)
open import LogOS.Domain.UniversalIR.Encoding as Enc using (natToBits; length)
open import LogOS.Domain.UniversalIR.Core.Minsky using (MinskyCode; prog; pc; r0; r1; r2; r3)
open import LogOS.Domain.UniversalIR.Core.Lambda using (LambdaCode; Term; term; var; lam; app)
open import LogOS.Domain.UniversalIR.Core.Ethereum using (EVMCode; code; stack; pc)
open import LogOS.Domain.UniversalIR.Core.QuantumOracle using (QuantumCode; prog; oracle; pc; r0; r1; r2; r3)
open import LogOS.Domain.UniversalIR.Core.QuantumCircuit using (QuantumCircuitCode; prog; pc; outLen; wires)
open import LogOS.Domain.UniversalIR.Core.UCode using (UCode; UM; UL; UE; UQ; UQC)

-- Lightweight size model for UniversalIR codes and inputs.

sizeNat : ℕ → ℕ
sizeNat n = length (natToBits n)

sizePATask : PATask → ℕ
sizePATask t =
  suc (sizeNat (Task.PATask.a t) + sizeNat (Task.PATask.b t))

sizeMinskyCode : MinskyCode → ℕ
sizeMinskyCode m =
  length (prog m) +
  sizeNat (pc m) +
  sizeNat (r0 m) +
  sizeNat (r1 m) +
  sizeNat (r2 m) +
  sizeNat (r3 m)

sizeLambdaTerm : Term → ℕ
sizeLambdaTerm (var _) = suc zero
sizeLambdaTerm (lam t) = suc (sizeLambdaTerm t)
sizeLambdaTerm (app t u) = suc (sizeLambdaTerm t + sizeLambdaTerm u)

sizeLambdaCode : LambdaCode → ℕ
sizeLambdaCode l = sizeLambdaTerm (term l)

sizeEVMCode : EVMCode → ℕ
sizeEVMCode e =
  length (code e) +
  length (stack e) +
  sizeNat (pc e)

sizeQuantumCode : QuantumCode → ℕ
sizeQuantumCode q =
  length (prog q) +
  length (oracle q) +
  sizeNat (pc q) +
  sizeNat (r0 q) +
  sizeNat (r1 q) +
  sizeNat (r2 q) +
  sizeNat (r3 q)

sizeQuantumCircuitCode : QuantumCircuitCode → ℕ
sizeQuantumCircuitCode q =
  length (prog q) +
  length (wires q) +
  sizeNat (pc q) +
  sizeNat (outLen q)

ucodeSize : UCode → ℕ
ucodeSize (UM m)  = sizeMinskyCode m
ucodeSize (UL l)  = sizeLambdaCode l
ucodeSize (UE e)  = sizeEVMCode e
ucodeSize (UQ q)  = sizeQuantumCode q
ucodeSize (UQC q) = sizeQuantumCircuitCode q
