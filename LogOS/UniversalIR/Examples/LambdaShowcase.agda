{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.UniversalIR.Examples.LambdaShowcase where

open import LogOS.Prelude
open import LogOS.Prelude using (ℕ)

open import LogOS.UniversalIR.Task using (PATask; mkTask; Mul; eval)
open import LogOS.UniversalIR.Core.Lambda using
  ( Term
  ; LambdaCode
  ; term
  ; church
  ; var
  ; lam
  ; app
  )
open import LogOS.UniversalIR.Core.UCode using (UL; simulate)
open import LogOS.UniversalIR.IR using (lowerToIR; decode)
open import LogOS.UniversalIR.Schemes using
  ( minskyScheme
  ; lambdaScheme
  ; ethereumScheme
  ; oracleScheme
  ; quantumCircuitScheme
  )
import LogOS.UniversalIR.Languages.Lambda as Lambda
import LogOS.Computation.Scheme as Sch
import LogOS.UniversalIR.Theorems as Thm

-- Raw vs certified Lambda: metrics + a five-paradigm output snapshot.

termSize : Term → ℕ
termSize (var _)   = suc zero
termSize (lam t)   = suc (termSize t)
termSize (app t u) = suc (termSize t + termSize u)

maxℕ : ℕ → ℕ → ℕ
maxℕ zero    n       = n
maxℕ (suc m) zero    = suc m
maxℕ (suc m) (suc n) = suc (maxℕ m n)

termDepth : Term → ℕ
termDepth (var _)   = suc zero
termDepth (lam t)   = suc (termDepth t)
termDepth (app t u) = suc (maxℕ (termDepth t) (termDepth u))

task : PATask
task = mkTask Mul 2 3

expected : ℕ
expected = eval task

expected≡6 : expected ≡ 6
expected≡6 = refl

rawCode : LambdaCode
rawCode = Lambda.compileRawBrand task

rawTerm : Term
rawTerm = term rawCode

rawFuel : ℕ
rawFuel = Lambda.fuel task

rawSize : ℕ
rawSize = termSize rawTerm

rawDepth : ℕ
rawDepth = termDepth rawTerm

-- Raw output after the default fuel; no correctness claim.
rawObserved : ℕ
rawObserved = decode (lowerToIR (simulate rawFuel (UL rawCode)))

certCode : LambdaCode
certCode = Lambda.compileBrand task

certTerm : Term
certTerm = term certCode

certFuel : ℕ
certFuel = Lambda.fuel task

certSize : ℕ
certSize = termSize certTerm

certDepth : ℕ
certDepth = termDepth certTerm

-- Certified output (scheme view).
certObserved : ℕ
certObserved = Sch.run lambdaScheme task

certTerm≡church : certTerm ≡ church expected
certTerm≡church = refl

interfaceCorrect : Thm.InterfaceSchemesCorrect task
interfaceCorrect = Thm.patask-interfaceSchemes-correct task

certObserved-ok : certObserved ≡ expected
certObserved-ok = Thm.InterfaceSchemesCorrect.lambda interfaceCorrect

certObserved≡6 : certObserved ≡ 6
certObserved≡6 = trans certObserved-ok expected≡6

record Outputs : Set where
  field
    minsky   : ℕ
    lambda   : ℕ
    ethereum : ℕ
    oracle   : ℕ
    circuit  : ℕ

outputs : Outputs
outputs =
  record
    { minsky   = Sch.run minskyScheme task
    ; lambda   = Sch.run lambdaScheme task
    ; ethereum = Sch.run ethereumScheme task
    ; oracle   = Sch.run oracleScheme task
    ; circuit  = Sch.run quantumCircuitScheme task
    }

minsky-ok : Sch.run minskyScheme task ≡ expected
minsky-ok = Thm.InterfaceSchemesCorrect.minsky interfaceCorrect

lambda-ok : Sch.run lambdaScheme task ≡ expected
lambda-ok = Thm.InterfaceSchemesCorrect.lambda interfaceCorrect

ethereum-ok : Sch.run ethereumScheme task ≡ expected
ethereum-ok = Thm.InterfaceSchemesCorrect.ethereum interfaceCorrect

oracle-ok : Sch.run oracleScheme task ≡ expected
oracle-ok = Thm.InterfaceSchemesCorrect.oracle interfaceCorrect

circuit-ok : Sch.run quantumCircuitScheme task ≡ expected
circuit-ok = Thm.InterfaceSchemesCorrect.circuit interfaceCorrect
