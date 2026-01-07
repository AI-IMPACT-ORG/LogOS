{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Examples.Addition where

open import LogOS.Prelude
open import Data.Nat using (ℕ)

open import LogOS.Domain.UniversalIR.Task
import LogOS.Computation.Scheme as Sch
open import LogOS.Domain.UniversalIR.Schemes using
  ( minskyMachineScheme
  ; lambdaMachineScheme
  ; ethereumMachineScheme
  ; oracleMachineScheme
  )
import LogOS.Domain.UniversalIR.Theorems as Thm

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
