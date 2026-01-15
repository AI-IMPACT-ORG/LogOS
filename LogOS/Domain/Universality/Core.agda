{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Universality.Core where

open import LogOS.Prelude
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)

-- A minimal, executable universality core. We give simple step semantics for each
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

-- Quantum: list length of gates; step pops one gate.
record CoreQuantumCode : Set where
  constructor mkCoreQ
  field gates : ℕ

open CoreQuantumCode public

stepCoreQ : CoreQuantumCode → CoreQuantumCode
stepCoreQ q with gates q
... | zero    = q
... | (suc n) = mkCoreQ n

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
