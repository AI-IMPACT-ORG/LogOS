{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Lab.All where

-- Stable lab surface for agents: socket + learning + networks + frameworks.
-- Experimental arguments, transformer emission, physics/RG-flow, and capstones
-- live in `LogOS.Packs.Agents.Experimental.Lab`.

module Lab where
  open import LogOS.Packs.Agents.Lab.Core public

module MetaLanguage where
  open import LogOS.Packs.Agents.MetaLanguage public

module Socket where
  open import LogOS.Packs.Agents.Socket.Ports public
  open import LogOS.Packs.Agents.Socket.Contracts public
  open import LogOS.Packs.Agents.Socket.Core public
  module HomOver where
    open import LogOS.Packs.Agents.Socket.HomOver public
  module Reindex where
    open import LogOS.Packs.Agents.Socket.Reindex public
  module FromLogicCoreSocket where
    open import LogOS.Packs.Agents.Socket.FromLogicCore public
  module FromKernelSocket where
    open import LogOS.Packs.Agents.Socket.FromKernel public
  module FromGradedKernelSocket where
    open import LogOS.Packs.Agents.Socket.FromGradedKernel public

module Learning where
  module Core where
    open import LogOS.Packs.Agents.Learning.Core public
  module TrainingSoundness where
    open import LogOS.Packs.Agents.Learning.TrainingSoundness public
  module Network where
    open import LogOS.Packs.Agents.Learning.Network public
  module EndoFixedPoint where
    open import LogOS.Packs.Agents.EndoFixedPoint public
  module FixedPoint where
    open import LogOS.Packs.Agents.Learning.FixedPoint public
  module SoftPolicy where
    open import LogOS.Packs.Agents.Learning.SoftPolicy public

module Safety where
  module Meaningfulness where
    open import LogOS.Packs.Agents.Safety.Meaningfulness public
  module Monitor where
    open import LogOS.Packs.Agents.Safety.Monitor public
  module Audit where
    open import LogOS.Packs.Agents.Safety.Audit public
  module NoTotalAuditor where
    open import LogOS.Packs.Agents.Safety.NoTotalAuditor public

module Telemetry where
  open import LogOS.Packs.Agents.Telemetry public

module Frameworks where
  open import LogOS.Packs.Agents.Frameworks.Core public
  open import LogOS.Packs.Agents.Frameworks.GodelMachine public
  open import LogOS.Packs.Agents.Frameworks.AIXI_Bounded public
  open import LogOS.Packs.Agents.Frameworks.OOPS public
  open import LogOS.Packs.Agents.Frameworks.MetaReasoning public
  open import LogOS.Packs.Agents.Frameworks.UniversalIR public
  open import LogOS.Packs.Agents.Frameworks.PATask public
  open import LogOS.Packs.Agents.Frameworks.PATaskAgreement public
  open import LogOS.Packs.Agents.Frameworks.KernelNative public

module Networks where
  module Core where
    open import LogOS.Packs.Agents.Networks.Core public
  module HeteroWiring where
    open import LogOS.Packs.Agents.Networks.Hetero public
  module NetworkAgent where
    open import LogOS.Packs.Agents.Networks.NetworkAgent public
  module Interop where
    open import LogOS.Packs.Agents.Networks.Interop public
  module MonitorInterop where
    open import LogOS.Packs.Agents.Networks.MonitorInterop public
  module Roles where
    open import LogOS.Packs.Agents.Networks.Roles public
  module Tensor where
    open import LogOS.Packs.Agents.Networks.Tensor public
  module NetworkSafety where
    open import LogOS.Packs.Agents.Networks.Safety public

module Comparisons where
  open import LogOS.Packs.Agents.Comparisons.Refinement public
  open import LogOS.Packs.Agents.Comparisons.Cost public
  open import LogOS.Packs.Agents.Comparisons.Limitations public

module Emit where
  module PythonSyntax where
    open import LogOS.Packs.Agents.Emit.Backends.Python.Syntax public
  -- Anchor the backend interface modules (reachability/discoverability).
  import LogOS.Packs.Agents.Emit.Backends.Python.Backend as PythonBackend
  import LogOS.Packs.Agents.Emit.IR.Backend as IRBackend
  import LogOS.Packs.Agents.Emit.IR.BackendSyntax as IRBackendSyntax
  import LogOS.Packs.Agents.Emit.IR.Features.TelemetryPlan as TelemetryPlan
  module Intent where
    open import LogOS.Packs.Agents.Emit.IR.Intent public
  module IntentExamples where
    open import LogOS.Packs.Agents.Emit.IR.IntentExamples public
  module IntentFactory where
    open import LogOS.Packs.Agents.Emit.IR.IntentFactory public

module Examples where
  module HelloSocket where
    open import LogOS.Packs.Agents.Examples.HelloSocket public
  module HelloNetwork where
    open import LogOS.Packs.Agents.Examples.HelloNetwork public
  module ReindexedNetwork where
    open import LogOS.Packs.Agents.Examples.ReindexedNetwork public
  module NeuralSymbolicBlend where
    open import LogOS.Packs.Agents.Examples.NeuralSymbolicBlend public
