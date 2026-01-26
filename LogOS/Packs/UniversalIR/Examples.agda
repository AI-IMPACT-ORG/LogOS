{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.UniversalIR.Examples where

-- Examples and worked developments for UniversalIR.
--
-- These are part of the *formal argument surface*: documentation imports this
-- module, and CI type-checks those docs. If an example breaks, the published
-- universality narrative is out of sync and fails the build.
--
-- This is deliberately separated from `Packs.UniversalIR.Core` so the “core
-- surface” stays import-light, while the checked evidence remains discoverable.

open import LogOS.Domain.UniversalIR.Examples.Addition public

module Multiplication where
  open import LogOS.Domain.UniversalIR.Examples.Multiplication public

module QuantumCircuit where
  open import LogOS.Domain.UniversalIR.Examples.QuantumCircuit public

module QuantumCircuitAmp where
  open import LogOS.Domain.UniversalIR.Examples.QuantumCircuitAmp public

module QuantumOracle where
  open import LogOS.Domain.UniversalIR.Examples.QuantumOracle public

module Convincing where
  open import LogOS.Domain.UniversalIR.Examples.Convincing public

module SchemeChoices where
  open import LogOS.Domain.UniversalIR.Examples.SchemeChoices public

module LambdaShowcase where
  open import LogOS.Domain.UniversalIR.Examples.LambdaShowcase public

module ArbitraryTasks where
  open import LogOS.Domain.UniversalIR.Examples.ArbitraryTasks public

module KernelDecodeLaxTasks where
  open import LogOS.Domain.UniversalIR.Examples.KernelDecodeLaxTasks public

module KernelSaturationLaxTasks where
  open import LogOS.Domain.UniversalIR.Examples.KernelSaturationLaxTasks public

module KernelSaturationLaxTasksNontrivial where
  open import LogOS.Domain.UniversalIR.Examples.KernelSaturationLaxTasksNontrivial public

module WhileExamples where
  module Factorial where
    open import LogOS.Domain.UniversalIR.While.Examples.Factorial public

  module CertifiedTranspile where
    open import LogOS.Domain.UniversalIR.While.Examples.CertifiedTranspile public
