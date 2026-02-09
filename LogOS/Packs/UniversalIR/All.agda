{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.UniversalIR.All where

-- UniversalIR pack:
-- - curated computational universality surface (“machines as schemes”)
-- - multi-paradigm agreement theorem
-- - kernel instance + boundary I/O views (graded boundary order is intentionally vacuous;
--   use observed-kernel ports for meaningful satisfaction)

open import LogOS.Packs.Trust using (PackTrust)
import LogOS.Packs.UniversalIR.Core as PackCore

packTrust : PackTrust
packTrust = PackCore.packTrust

module AssumptionBundles where
  open import LogOS.Packs.Assumptions.Universality public

module Core where
  open import LogOS.Packs.UniversalIR.Core public

module Agreement where
  open import LogOS.Packs.UniversalIR.Agreement public

module CHL where
  open import LogOS.Packs.UniversalIR.CHLAdequacyInstances public

module Algorithms where
  open import LogOS.Packs.UniversalIR.Pack public

module Examples where
  open import LogOS.Packs.UniversalIR.Examples public

-- Optional, stable namespaces (not part of the minimal Core “math object” layer).

module Theorems where
  import LogOS.UniversalIR.Theorems as Theoremsₜ
  module Bundle = Theoremsₜ

module Languages where
  import LogOS.UniversalIR.Languages.Minsky as Minskyₜ
  import LogOS.UniversalIR.Languages.Lambda as Lambdaₜ
  import LogOS.UniversalIR.Languages.Ethereum as Ethereumₜ
  import LogOS.UniversalIR.Languages.QuantumOracle as QuantumOracleₜ
  import LogOS.UniversalIR.Languages.QuantumCircuit as QuantumCircuitₜ
  import LogOS.UniversalIR.Core.QuantumCircuitAmp as QuantumCircuitAmpₜ

  module Minsky = Minskyₜ
  module Lambda = Lambdaₜ
  module Ethereum = Ethereumₜ
  module QuantumOracle = QuantumOracleₜ
  module QuantumCircuit = QuantumCircuitₜ
  module QuantumCircuitAmp = QuantumCircuitAmpₜ

module Physics where
  import LogOS.UniversalIR.Physics.Implementable as Implementableₜ
  module Implementable = Implementableₜ

module While where
  import LogOS.UniversalIR.While.Language as Languageₜ
  import LogOS.UniversalIR.While.Semantics as Semanticsₜ
  import LogOS.UniversalIR.While.Compile as Compileₜ
  import LogOS.UniversalIR.While.Decompile as Decompileₜ
  import LogOS.UniversalIR.While.Theorems as Theoremsₜ

  module Language = Languageₜ
  module Semantics = Semanticsₜ
  module Compile = Compileₜ
  module Decompile = Decompileₜ
  module TheoremsWhile = Theoremsₜ

module Scaffold where
  -- Explicit access to a deliberately vacuous kernel instance and its structural
  -- wiring. This is kept under `Scaffold` to avoid accidental semantic drift:
  -- stable users should prefer `Meaningfulness` (observed-kernel ports).
  open import LogOS.Packs.UniversalIR.Kernel public

-- “What is nontrivial here?” helpers:
-- - `Scaffold` exposes a deliberately vacuous graded kernel instance.
-- - `Meaningfulness` exposes the observed-kernel ports used for meaningful
--   satisfaction/observation stories.

module Vacuity where
  open Scaffold public using (topOrderU; vacuousHTruth)

module Meaningfulness where
  open Scaffold.ObservedPorts public

module Applications where
  open import LogOS.Packs.UniversalIR.Applications.All public
