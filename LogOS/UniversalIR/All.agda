{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.UniversalIR.All where

-- Index module for the UniversalIR domain (discoverability only).

import LogOS.UniversalIR.Core as Coreₜ
import LogOS.UniversalIR.Pack as Packₜ
import LogOS.UniversalIR.IR as IRₜ
import LogOS.UniversalIR.Std as Stdₜ
import LogOS.UniversalIR.Encoding as Encodingₜ
import LogOS.UniversalIR.Backend as Backendₜ
import LogOS.UniversalIR.Schemes as Schemesₜ
import LogOS.UniversalIR.Task as Taskₜ
import LogOS.UniversalIR.ArbitraryTasks as ArbitraryTasksₜ
import LogOS.UniversalIR.TasksToUProcess as TasksToUProcessₜ
import LogOS.UniversalIR.Theorems as Theoremsₜ
import LogOS.UniversalIR.TheoremsExpr as TheoremsExprₜ
import LogOS.UniversalIR.CompilerCorrectness as CompilerCorrectnessₜ
import LogOS.UniversalIR.Futamura as Futamuraₜ
import LogOS.UniversalIR.KernelRichG as KernelRichGₜ
import LogOS.UniversalIR.ObservedKernel as ObservedKernelₜ
import LogOS.UniversalIR.Universality as Universalityₜ
import LogOS.UniversalIR.Blum as Blumₜ
import LogOS.UniversalIR.Size as Sizeₜ

import LogOS.UniversalIR.Core.All as CoreAllₜ
import LogOS.UniversalIR.Languages.All as Languagesₜ
import LogOS.UniversalIR.Examples.All as Examplesₜ
import LogOS.UniversalIR.While.All as Whileₜ
import LogOS.UniversalIR.Quantum.Measurement as QuantumMeasurementₜ
import LogOS.UniversalIR.Physics.Implementable as PhysicsImplementableₜ
import LogOS.UniversalIR.CQM.QuantumCircuitRel as CQMQuantumCircuitRelₜ

module Core = Coreₜ
module Pack = Packₜ
module IR = IRₜ
module Std = Stdₜ
module Encoding = Encodingₜ
module Backend = Backendₜ
module Schemes = Schemesₜ
module Task = Taskₜ
module ArbitraryTasks = ArbitraryTasksₜ
module TasksToUProcess = TasksToUProcessₜ
module Theorems = Theoremsₜ
module TheoremsExpr = TheoremsExprₜ
module CompilerCorrectness = CompilerCorrectnessₜ
module Futamura = Futamuraₜ
module KernelRichG = KernelRichGₜ
module ObservedKernel = ObservedKernelₜ
module Universality = Universalityₜ
module Blum = Blumₜ
module Size = Sizeₜ

module CoreAll = CoreAllₜ
module Languages = Languagesₜ
module Examples = Examplesₜ
module While = Whileₜ

module Quantum where
  module Measurement = QuantumMeasurementₜ

module Physics where
  module Implementable = PhysicsImplementableₜ

module CQM where
  module QuantumCircuitRel = CQMQuantumCircuitRelₜ
