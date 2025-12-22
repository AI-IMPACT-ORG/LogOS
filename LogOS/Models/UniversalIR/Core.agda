{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Models.UniversalIR.Core where

-- Curated, stable UniversalIR surface (no demo wiring).

open import LogOS.Domain.UniversalIR.IR public
open import LogOS.Domain.UniversalIR.Encoding public
open import LogOS.Domain.UniversalIR.Backend public
open import LogOS.Domain.UniversalIR.Core public
open import LogOS.Domain.UniversalIR.Std public
open import LogOS.Domain.UniversalIR.Blum public
open import LogOS.Domain.UniversalIR.Task public
open import LogOS.Domain.UniversalIR.Schemes public
open import LogOS.Domain.UniversalIR.Universality public

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
  -- - `NoOmniscience`: diagonal obstruction to total observers/deciders.
  -- - `BudgetedSeparationOutput`: quantitative “no total oracle within budget”.
  open import LogOS.Computation.SchemeCategory public
    using (run≤-map; run≤-meaning-comm; ComputesWithin-map; ComputesTo-map)
  open import LogOS.Computation.SchemeCategory public
    using (module ProcessCategory; module Semantics)
  open import LogOS.Computation.Scheme public
    using (FuelHalts; module Bridge)
  open import LogOS.Theorems.Meta.NoOmniscience public
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

  -- Note: intentionally no `Quantum` alias re-export here; use `QuantumOracle`
  -- or `QuantumCircuit` explicitly to avoid ambiguity.

module Physics where
  open import LogOS.Domain.UniversalIR.Physics.Implementable public

module While where
  open import LogOS.Domain.UniversalIR.While.Language public
  open import LogOS.Domain.UniversalIR.While.Semantics public
  open import LogOS.Domain.UniversalIR.While.Compile public
  open import LogOS.Domain.UniversalIR.While.Decompile public
  open import LogOS.Domain.UniversalIR.While.Theorems public
