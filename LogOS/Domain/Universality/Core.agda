{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Universality.Core where

open import LogOS.Prelude
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)

-- A tiny, executable universality core. We give simple step semantics for each
-- paradigm and a unified sum type with a common step function. This is intended
-- to be pristine: total, documented, and uniform.

-- Turing/Minsky: toy register machine state (pc, reg)
-- Turing/Minsky: toy register machine with a single register and program counter.
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
record ToyQuantumCode : Set where
  constructor mkToyQ
  field gates : ℕ

open ToyQuantumCode public

stepToyQ : ToyQuantumCode → ToyQuantumCode
stepToyQ q with gates q
... | zero    = q
... | (suc n) = mkToyQ n

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

data ToyUCode : Set where
  ToyT : TuringCode     → ToyUCode
  ToyC : ChurchCode     → ToyUCode
  ToyQ : ToyQuantumCode → ToyUCode
  ToyB : ChainCode      → ToyUCode

stepToyU : ToyUCode → ToyUCode
stepToyU (ToyT t) = ToyT (stepT t)
stepToyU (ToyC c) = ToyC (stepC c)
stepToyU (ToyQ q) = ToyQ (stepToyQ q)
stepToyU (ToyB b) = ToyB (stepB b)

simulateToy : ℕ → ToyUCode → ToyUCode
simulateToy zero    u = u
simulateToy (suc n) u = simulateToy n (stepToyU u)
