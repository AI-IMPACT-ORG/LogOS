{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.CompilerCorrectness where

-- Canonical compiler-correctness packaging for the UniversalIR story.

open import LogOS.Prelude

open import LogOS.Domain.UniversalIR.Core using
  ( UCode
  ; UM; UL; UE; UQ; UQC
  ; MinskyCode; LambdaCode; EVMCode; QuantumCode; QuantumCircuitCode
  ; simulate
  )
open import LogOS.Domain.UniversalIR.IR using (lowerToIR; decode; observe)
open import LogOS.Domain.UniversalIR.Task using (PATask; eval)
import LogOS.Domain.UniversalIR.Languages.Minsky as Minsky
import LogOS.Domain.UniversalIR.Languages.Lambda as Lambda
import LogOS.Domain.UniversalIR.Languages.Ethereum as Ether
import LogOS.Domain.UniversalIR.Languages.QuantumOracle as Oracle
import LogOS.Domain.UniversalIR.Languages.QuantumCircuit as Circuit
import LogOS.Domain.UniversalIR.Theorems as Thm

record CompilerCorrectness
  {ℓI ℓC ℓO : Level}
  (Input : Set ℓI)
  (Code  : Set ℓC)
  (Out   : Set ℓO)
  (compile : Input → Code)
  (run : Code → Out)
  (spec : Input → Out)
  : Set (lsuc (ℓI ⊔ ℓC ⊔ ℓO)) where
  field
    correct : ∀ x → run (compile x) ≡ spec x

runU : ℕ → UCode → ℕ
runU fuel u = decode (lowerToIR (simulate fuel u))

runU-observe
  : ∀ fuel u
  → runU fuel u ≡ observe (simulate fuel u)
runU-observe _ _ = refl

compiler-correct-observe
  : ∀ {ℓI}
    {Input : Set ℓI}
    (compile : Input → UCode)
    (fuel : Input → ℕ)
    (spec : Input → ℕ)
  → (∀ x → runU (fuel x) (compile x) ≡ spec x)
  → (∀ x → observe (simulate (fuel x) (compile x)) ≡ spec x)
compiler-correct-observe _ _ _ correct x = correct x

runMinsky : MinskyCode × ℕ → ℕ
runMinsky (code , fuel) = runU fuel (UM code)

runLambda : LambdaCode × ℕ → ℕ
runLambda (code , fuel) = runU fuel (UL code)

runEthereum : EVMCode × ℕ → ℕ
runEthereum (code , fuel) = runU fuel (UE code)

runOracle : QuantumCode × ℕ → ℕ
runOracle (code , fuel) = runU fuel (UQ code)

runCircuit : QuantumCircuitCode × ℕ → ℕ
runCircuit (code , fuel) = runU fuel (UQC code)

minsky-compile : PATask → MinskyCode × ℕ
minsky-compile t = (Minsky.compileBrand t , Minsky.fuel t)

lambda-compile : PATask → LambdaCode × ℕ
lambda-compile t = (Lambda.compileBrand t , Lambda.fuel t)

ethereum-compile : PATask → EVMCode × ℕ
ethereum-compile t = (Ether.compileBrand t , Ether.fuel t)

oracle-compile : PATask → QuantumCode × ℕ
oracle-compile t = (Oracle.compileBrand t , Oracle.fuel t)

circuit-compile : PATask → QuantumCircuitCode × ℕ
circuit-compile t = (Circuit.compileBrand t , Circuit.fuel t)

minsky-compiler : CompilerCorrectness PATask (MinskyCode × ℕ) ℕ
  minsky-compile runMinsky eval
minsky-compiler = record { correct = Thm.minsky-correct }

lambda-compiler : CompilerCorrectness PATask (LambdaCode × ℕ) ℕ
  lambda-compile runLambda eval
lambda-compiler = record { correct = Thm.lambda-correct }

ethereum-compiler : CompilerCorrectness PATask (EVMCode × ℕ) ℕ
  ethereum-compile runEthereum eval
ethereum-compiler = record { correct = Thm.ethereum-correct }

oracle-compiler : CompilerCorrectness PATask (QuantumCode × ℕ) ℕ
  oracle-compile runOracle eval
oracle-compiler = record { correct = Thm.oracle-correct }

circuit-compiler : CompilerCorrectness PATask (QuantumCircuitCode × ℕ) ℕ
  circuit-compile runCircuit eval
circuit-compiler = record { correct = Thm.circuit-correct }
