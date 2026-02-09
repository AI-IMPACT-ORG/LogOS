{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.UniversalIR.CompilerCorrectness where

-- Canonical compiler-correctness packaging for the UniversalIR story.

open import LogOS.Prelude

open import LogOS.UniversalIR.Core using
  ( UCode
  ; UM; UL; UE; UQ; UQC
  ; MinskyCode; LambdaCode; EVMCode; QuantumCode; QuantumCircuitCode
  ; simulate
  )
open import LogOS.UniversalIR.IR using (lowerToIR; decode; observe)
open import LogOS.UniversalIR.Task using (PATask; eval; PAExprTask; evalExprTask)
import LogOS.Computation.Scheme as Sch
open import LogOS.UniversalIR.Schemes using
  ( minskyMachineScheme
  ; lambdaMachineScheme
  ; ethereumMachineScheme
  ; oracleMachineScheme
  ; quantumCircuitMachineScheme
  )
import LogOS.UniversalIR.Languages.Minsky as Minsky
import LogOS.UniversalIR.Languages.Lambda as Lambda
import LogOS.UniversalIR.Languages.Ethereum as Ether
import LogOS.UniversalIR.Languages.QuantumOracle as Oracle
import LogOS.UniversalIR.Languages.QuantumCircuit as Circuit
import LogOS.UniversalIR.Theorems as Thm
import LogOS.UniversalIR.TheoremsExpr as ThmExpr

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

record SchemeCorrectness
  {ℓI ℓO ℓC ℓQ : Level}
  (Input : Set ℓI)
  (Output : Set ℓO)
  (S : Sch.Scheme {ℓI = ℓI} {ℓO = ℓO} {ℓC = ℓC} {ℓQ = ℓQ} Input Output)
  (spec : Input → Output)
  : Set (lsuc (ℓI ⊔ ℓO ⊔ ℓC ⊔ ℓQ)) where
  field
    correct : ∀ x → Sch.run S x ≡ spec x

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

minsky-scheme-correct : SchemeCorrectness PATask ℕ minskyMachineScheme eval
minsky-scheme-correct =
  record { correct = Thm.minskyMachine-correct }

lambda-scheme-correct : SchemeCorrectness PATask ℕ lambdaMachineScheme eval
lambda-scheme-correct =
  record { correct = Thm.lambdaMachine-correct }

ethereum-scheme-correct : SchemeCorrectness PATask ℕ ethereumMachineScheme eval
ethereum-scheme-correct =
  record { correct = Thm.ethereumMachine-correct }

oracle-scheme-correct : SchemeCorrectness PATask ℕ oracleMachineScheme eval
oracle-scheme-correct =
  record { correct = Thm.oracleMachine-correct }

circuit-scheme-correct : SchemeCorrectness PATask ℕ quantumCircuitMachineScheme eval
circuit-scheme-correct =
  record { correct = Thm.circuitMachine-correct }

-- Expression-fragment compilers (PAExprTask): canonical surface re-export.

runMinskyExpr : MinskyCode → ℕ
runMinskyExpr code = runU zero (UM code)

runLambdaExpr : LambdaCode → ℕ
runLambdaExpr code = runU zero (UL code)

runEthereumExpr : EVMCode → ℕ
runEthereumExpr code = runU zero (UE code)

runOracleExpr : QuantumCode → ℕ
runOracleExpr code = runU zero (UQ code)

runCircuitExpr : QuantumCircuitCode → ℕ
runCircuitExpr code = runU zero (UQC code)

minsky-expr-compile : PAExprTask → MinskyCode
minsky-expr-compile = ThmExpr.compileMinskyExpr

lambda-expr-compile : PAExprTask → LambdaCode
lambda-expr-compile = ThmExpr.compileLambdaExpr

ethereum-expr-compile : PAExprTask → EVMCode
ethereum-expr-compile = ThmExpr.compileEthereumExpr

oracle-expr-compile : PAExprTask → QuantumCode
oracle-expr-compile = ThmExpr.compileOracleExpr

circuit-expr-compile : PAExprTask → QuantumCircuitCode
circuit-expr-compile = ThmExpr.compileCircuitExpr

minsky-expr-compiler : CompilerCorrectness PAExprTask MinskyCode ℕ
  minsky-expr-compile runMinskyExpr evalExprTask
minsky-expr-compiler = record { correct = ThmExpr.minskyExprMachine-correct }

lambda-expr-compiler : CompilerCorrectness PAExprTask LambdaCode ℕ
  lambda-expr-compile runLambdaExpr evalExprTask
lambda-expr-compiler = record { correct = ThmExpr.lambdaExprMachine-correct }

ethereum-expr-compiler : CompilerCorrectness PAExprTask EVMCode ℕ
  ethereum-expr-compile runEthereumExpr evalExprTask
ethereum-expr-compiler = record { correct = ThmExpr.ethereumExprMachine-correct }

oracle-expr-compiler : CompilerCorrectness PAExprTask QuantumCode ℕ
  oracle-expr-compile runOracleExpr evalExprTask
oracle-expr-compiler = record { correct = ThmExpr.oracleExprMachine-correct }

circuit-expr-compiler : CompilerCorrectness PAExprTask QuantumCircuitCode ℕ
  circuit-expr-compile runCircuitExpr evalExprTask
circuit-expr-compiler = record { correct = ThmExpr.quantumCircuitExprMachine-correct }

minsky-expr-scheme-correct
  : SchemeCorrectness PAExprTask ℕ ThmExpr.minskyExprMachineScheme evalExprTask
minsky-expr-scheme-correct =
  record { correct = ThmExpr.minskyExprMachine-correct }

lambda-expr-scheme-correct
  : SchemeCorrectness PAExprTask ℕ ThmExpr.lambdaExprMachineScheme evalExprTask
lambda-expr-scheme-correct =
  record { correct = ThmExpr.lambdaExprMachine-correct }

ethereum-expr-scheme-correct
  : SchemeCorrectness PAExprTask ℕ ThmExpr.ethereumExprMachineScheme evalExprTask
ethereum-expr-scheme-correct =
  record { correct = ThmExpr.ethereumExprMachine-correct }

oracle-expr-scheme-correct
  : SchemeCorrectness PAExprTask ℕ ThmExpr.oracleExprMachineScheme evalExprTask
oracle-expr-scheme-correct =
  record { correct = ThmExpr.oracleExprMachine-correct }

circuit-expr-scheme-correct
  : SchemeCorrectness PAExprTask ℕ ThmExpr.quantumCircuitExprMachineScheme evalExprTask
circuit-expr-scheme-correct =
  record { correct = ThmExpr.quantumCircuitExprMachine-correct }
