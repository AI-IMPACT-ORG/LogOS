{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Examples.Multiplication where

open import LogOS.Prelude
open import LogOS.Prelude.Nat using (ℕ)

open import LogOS.Domain.UniversalIR.Task
import LogOS.Computation.Scheme as Sch
open import LogOS.Domain.UniversalIR.Schemes using
  ( minskyMachineScheme
  ; lambdaMachineScheme
  ; ethereumMachineScheme
  ; oracleMachineScheme
  )
import LogOS.Domain.UniversalIR.Theorems as Thm

-- EXAMPLE (argument): multiplication agreement across representations and schemes.

-- A single concrete PA task (multiplication) executed in four paradigms.

task : PATask
task = mkTask Mul 2 3

answer : ℕ
answer = eval task

-- For this concrete closed task, each backend computes the PA answer.

minsky-ok : Sch.run minskyMachineScheme task ≡ answer
minsky-ok = Thm.minskyMachine-correct task

lambda-ok : Sch.run lambdaMachineScheme task ≡ answer
lambda-ok = Thm.lambdaMachine-correct task

ethereum-ok : Sch.run ethereumMachineScheme task ≡ answer
ethereum-ok = Thm.ethereumMachine-correct task

oracle-ok : Sch.run oracleMachineScheme task ≡ answer
oracle-ok = Thm.oracleMachine-correct task
