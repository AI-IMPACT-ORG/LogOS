{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.UniversalIR.Kernel where

open import LogOS.Prelude

open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.API.Assumptions.Core using (LogicCore; coreFromGradedKernel)
import LogOS.Packs.Assumptions.Universality as AssumpUni

open import LogOS.Packs.Trust using (PackTrust; scaffold)

-- Trust note: this module primarily exposes *structural wiring* around a
-- deliberately vacuous kernel instance (`topOrderU`, `vacuousHTruth`). Treat it
-- as scaffold infrastructure unless you additionally supply non-vacuity guards
-- via the observed-kernel ports below.
packTrust : PackTrust
packTrust = record { level = scaffold }

open import LogOS.UniversalIR.KernelRichG public using
  (Sig; Q; GUKR; topOrderU; vacuousHTruth)
open import LogOS.UniversalIR.ObservedKernel public
open import LogOS.Kernel.Graded using (GradedKernel)
import LogOS.Boundary.FromGradedKernel as GB
open import LogOS.Boundary.IO using (BoundaryIO)
open import LogOS.Boundary.MultiIO using (MultiBoundaryIO; defaultMultiBoundaryIOFromBoundaryIO)

-- Curated access to the graded kernel instance over UniversalIR,
-- the observed-kernel kits, and default Boundary IO views.
--
-- Note: the graded kernel instance `GUKR` is deliberately order-vacuous on the
-- boundary (see `topOrderU`) and has vacuous H-tier truth (see `vacuousHTruth`).
-- Use `ObservedPorts.*` for meaningful satisfaction/observation stories.

-- Threaded assumptions view: expose a shared `LogicCore` and the minimal
-- Universality bundle instance (choosing the neutral step grade).
core : LogicCore {lzero}
core = coreFromGradedKernel GUKR

universality : AssumpUni.UniversalityBundle core
universality = record { stepGrade = QAdapter.e (LogicCore.Q core) }

boundaryIO
  : BoundaryIO Sig Q (GradedKernel.HWorld GUKR) (GradedKernel.BB GUKR) (GradedKernel.HTruth GUKR)
boundaryIO = GB.boundaryIO GUKR

multiBoundaryIO
  : ∀ {Role : Set} → MultiBoundaryIO Role Sig Q (GradedKernel.HWorld GUKR) (GradedKernel.BB GUKR) (GradedKernel.HTruth GUKR)
multiBoundaryIO {Role} =
  defaultMultiBoundaryIOFromBoundaryIO {Role = Role} boundaryIO

-- Canonical port views for observed-kernel kits.
module ObservedPorts where
  module For = Ports
  module Code = Ports CodeObsKit
  module Lambda = Ports LambdaObsKit
  module Minsky = Ports MinskyObsKit
  module Ethereum = Ports EthereumObsKit
  module QuantumOracle = Ports QuantumOracleObsKit
  module QuantumCircuit = Ports QuantumCircuitObsKit
