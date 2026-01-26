{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Examples.Convincing where

open import LogOS.Prelude
open import LogOS.Prelude.Nat using (ℕ)

open import LogOS.Domain.UniversalIR.Task
import LogOS.Computation.Scheme as Sch
open import LogOS.Domain.UniversalIR.Schemes using (minskyMachineScheme; ethereumMachineScheme)
import LogOS.Domain.UniversalIR.Theorems as Thm

-- EXAMPLE (argument): compact “many paradigms agree” witness for concrete tasks.

-- A skeptic-facing non-trivial fact: two different Turing-complete backends
-- (Minsky machines and an EVM-like stack machine) both compute the PA meaning
-- of every task in this library fragment, and therefore agree for all inputs.

minsky-sound : (t : PATask) → Sch.run minskyMachineScheme t ≡ eval t
minsky-sound = Thm.minskyMachine-correct

ethereum-sound : (t : PATask) → Sch.run ethereumMachineScheme t ≡ eval t
ethereum-sound = Thm.ethereumMachine-correct

m≡e : (t : PATask) → Sch.run minskyMachineScheme t ≡ Sch.run ethereumMachineScheme t
m≡e t = trans (minsky-sound t) (sym (ethereum-sound t))

-- One concrete example (multiplication) as an easy sanity check.

task : PATask
task = mkTask Mul 2 3

answer : ℕ
answer = eval task

mOk : Sch.run minskyMachineScheme task ≡ answer
mOk = minsky-sound task

eOk : Sch.run ethereumMachineScheme task ≡ answer
eOk = ethereum-sound task
