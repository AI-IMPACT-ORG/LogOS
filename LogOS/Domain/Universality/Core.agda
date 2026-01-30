{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Universality.Core where

open import LogOS.Prelude
open import LogOS.Prelude.Nat using (ℕ; zero; suc)
open import LogOS.Prelude.Sum using (_⊎_; inj₁; inj₂)
open import LogOS.Prelude.List using (List; []; _∷_)
import LogOS.Domain.UniversalIR.Core.QuantumCircuit as QC
open QC.QuantumCircuitCode public

-- A minimal, executable universal-logic core. We give simple step semantics for each
-- paradigm and a unified sum type with a common step function. This is intended
-- to be pristine: total, documented, and uniform.

-- Turing/Minsky: minimal register machine state (pc, reg)
-- Turing/Minsky: minimal register machine with a single register and program counter.
-- Step increments pc; if reg > 0, it decrements reg by 1 (simple progress).

record TuringCode : Set where
  constructor mkT
  field pc reg : ℕ

open TuringCode public

stepT : TuringCode → TuringCode
stepT t with reg t
... | zero    = mkT (suc (pc t)) zero
... | (suc r) = mkT (suc (pc t)) r

-- Church (λ-calculus): use a size/depth counter; step contracts by 1 if > 0.
record ChurchCode : Set where
  constructor mkC
  field size : ℕ

open ChurchCode public

stepC : ChurchCode → ChurchCode
stepC c with size c
... | zero    = c
... | (suc n) = mkC n

-- Quantum: use the explicit basis-state circuit code.
--
-- This keeps the universality core minimal while making the quantum branch
-- directly executable (it reuses the `UniversalIR` quantum-circuit core).

CoreQuantumCode : Set
CoreQuantumCode = QC.QuantumCircuitCode

coreQProg : ℕ → List QC.QCInstr
coreQProg zero = QC.QCHALT ∷ []
coreQProg (suc n) = QC.QNOP ∷ coreQProg n

mkCoreQ : ℕ → CoreQuantumCode
mkCoreQ n = QC.mkQC 0 0 [] (coreQProg n)

mkCoreQAt : ℕ → ℕ → CoreQuantumCode
mkCoreQAt n pc = QC.mkQC pc 0 [] (coreQProg n)

stepCoreQ : CoreQuantumCode → CoreQuantumCode
stepCoreQ = QC.stepQC

-- Blockchain (EVM-like): program counter + gas; step increments pc and decrements gas.
record ChainCode : Set where
  constructor mkB
  field pc gas : ℕ

open ChainCode public

stepB : ChainCode → ChainCode
stepB s with gas s
... | zero    = s
... | (suc g) = mkB (suc (pc s)) g

-- Unified code and step

data CoreUCode : Set where
  CoreT : TuringCode     → CoreUCode
  CoreC : ChurchCode     → CoreUCode
  CoreQ : CoreQuantumCode → CoreUCode
  CoreB : ChainCode      → CoreUCode

stepCoreU : CoreUCode → CoreUCode
stepCoreU (CoreT t) = CoreT (stepT t)
stepCoreU (CoreC c) = CoreC (stepC c)
stepCoreU (CoreQ q) = CoreQ (stepCoreQ q)
stepCoreU (CoreB b) = CoreB (stepB b)

simulateCoreU : ℕ → CoreUCode → CoreUCode
simulateCoreU zero    u = u
simulateCoreU (suc n) u = simulateCoreU n (stepCoreU u)

-- Canonical observation: collapse each branch to a single ℕ observable.
observeCore : CoreUCode → ℕ
observeCore (CoreT t) = reg t
observeCore (CoreC c) = size c
observeCore (CoreQ q) = pc q
observeCore (CoreB b) = gas b

-- Canonical representative for the observed part (Church branch).
canonCore : CoreUCode → CoreUCode
canonCore u = CoreC (mkC (observeCore u))

-- Executable universal logic: a name for running the core stepper.
execCoreU : ℕ → CoreUCode → CoreUCode
execCoreU = simulateCoreU
