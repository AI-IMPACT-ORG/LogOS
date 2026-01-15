{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.UniversalIR.Core where

-- Curated, stable UniversalIR surface (no demo wiring).

open import LogOS.Domain.UniversalIR.IR public
open import LogOS.Domain.UniversalIR.Encoding public
open import LogOS.Domain.UniversalIR.Backend public
open import LogOS.Domain.UniversalIR.Core public
open import LogOS.Domain.UniversalIR.Std public
open import LogOS.Domain.UniversalIR.Blum public
open import LogOS.Domain.UniversalIR.Task public
open import LogOS.Domain.UniversalIR.CompilerCorrectness public
open import LogOS.Domain.UniversalIR.Schemes public
open import LogOS.Domain.UniversalIR.Universality public
open import LogOS.Packs.UniversalIR.RefinementInitiality public

-- Recommended runner for grade-indexed execution (“machines as schemes”).
open import LogOS.Computation.Scheme public using (run≤)

module Theorems where
  open import LogOS.Domain.UniversalIR.Theorems public

module Algorithms where
  -- First-class separation: `Algorithm` (spec) vs `Scheme` (implementation),
  -- packaged via the Assumptions/Claim/Pack/mkPack quartet.
  open import LogOS.Domain.UniversalIR.Pack public

module Guardrails where
  -- General CS-style invariants and barrier theorems that apply to the
  -- “machines as schemes” story.
  --
  -- - `run≤-map` / `run≤-meaning-comm`: representation invariance for
  --   grade-indexed execution (categorical sneak peek).
  -- - `Tarski`/`Diagonal`: diagonal obstruction to total observers/deciders.
  -- - `BudgetedSeparationOutput`: quantitative “no total oracle within budget”.
  open import LogOS.Computation.SchemeCategory public
    using (run≤-map; run≤-meaning-comm; ComputesWithin-map; ComputesTo-map; module ProcessCategory; module Semantics)
  open import LogOS.Computation.Scheme public
    using (FuelHalts; module Bridge)
  open import LogOS.Theorems.Meta.SpectralSeparationOutput public
  open import LogOS.Theorems.Meta.Tarski public using (undef-classical)
  open import LogOS.Theorems.Meta.Assumptions.Diagonal public using (noOmniscientDeciderC)
  open import LogOS.Theorems.Meta.BudgetedSeparationOutput public

module Languages where
  module Minsky where
    open import LogOS.Domain.UniversalIR.Languages.Minsky public

  module Lambda where
    open import LogOS.Domain.UniversalIR.Languages.Lambda public

  module Ethereum where
    open import LogOS.Domain.UniversalIR.Languages.Ethereum public

  module QuantumOracle where
    open import LogOS.Domain.UniversalIR.Languages.QuantumOracle public

  module QuantumCircuit where
    open import LogOS.Domain.UniversalIR.Languages.QuantumCircuit public

  module QuantumCircuitAmp where
    open import LogOS.Domain.UniversalIR.Core.QuantumCircuitAmp public

  -- Note: intentionally no `Quantum` alias re-export here; use `QuantumOracle`
  -- or `QuantumCircuit` explicitly to avoid ambiguity.

module Physics where
  open import LogOS.Domain.UniversalIR.Physics.Implementable public

module Kernel where
  open import LogOS.Packs.UniversalIR.Kernel public

module While where
  open import LogOS.Domain.UniversalIR.While.Language public
  open import LogOS.Domain.UniversalIR.While.Semantics public
  open import LogOS.Domain.UniversalIR.While.Compile public
  open import LogOS.Domain.UniversalIR.While.Decompile public
  open import LogOS.Domain.UniversalIR.While.Theorems public
