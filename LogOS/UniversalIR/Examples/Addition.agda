{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.UniversalIR.Examples.Addition where

open import LogOS.Prelude
open import LogOS.Prelude using (ℕ)

open import LogOS.UniversalIR.Task
import LogOS.Computation.Scheme as Sch
open import LogOS.UniversalIR.Schemes using
  ( minskyMachineScheme
  ; lambdaMachineScheme
  ; ethereumMachineScheme
  ; oracleMachineScheme
  )
import LogOS.UniversalIR.Theorems as Thm

-- EXAMPLE (argument): small end-to-end addition agreement across representations.

-- A single concrete PA task (addition) executed in four paradigms, each viewed
-- as a Scheme (machine = process + choice).

task : PATask
task = mkTask Add 2 3

answer : ℕ
answer = eval task

-- For this concrete closed task, each backend computes the PA answer.

minsky-ok : Sch.run minskyMachineScheme task ≡ answer
minsky-ok = Thm.minskyMachine-correct task

-- Lambda is included as a first-class scheme; correctness is now theorem-backed.
lambda-ok : Sch.run lambdaMachineScheme task ≡ answer
lambda-ok = Thm.lambdaMachine-correct task

ethereum-ok : Sch.run ethereumMachineScheme task ≡ answer
ethereum-ok = Thm.ethereumMachine-correct task

oracle-ok : Sch.run oracleMachineScheme task ≡ answer
oracle-ok = Thm.oracleMachine-correct task
