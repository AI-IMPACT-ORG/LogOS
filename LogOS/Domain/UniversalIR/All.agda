{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.All where

-- Index module for the UniversalIR domain (discoverability only).

import LogOS.Domain.UniversalIR.Core as Coreₜ
import LogOS.Domain.UniversalIR.Pack as Packₜ
import LogOS.Domain.UniversalIR.IR as IRₜ
import LogOS.Domain.UniversalIR.Std as Stdₜ
import LogOS.Domain.UniversalIR.Encoding as Encodingₜ
import LogOS.Domain.UniversalIR.Backend as Backendₜ
import LogOS.Domain.UniversalIR.Schemes as Schemesₜ
import LogOS.Domain.UniversalIR.Task as Taskₜ
import LogOS.Domain.UniversalIR.ArbitraryTasks as ArbitraryTasksₜ
import LogOS.Domain.UniversalIR.TasksToUProcess as TasksToUProcessₜ
import LogOS.Domain.UniversalIR.Theorems as Theoremsₜ
import LogOS.Domain.UniversalIR.TheoremsExpr as TheoremsExprₜ
import LogOS.Domain.UniversalIR.CompilerCorrectness as CompilerCorrectnessₜ
import LogOS.Domain.UniversalIR.KernelRichG as KernelRichGₜ
import LogOS.Domain.UniversalIR.ObservedKernel as ObservedKernelₜ
import LogOS.Domain.UniversalIR.Universality as Universalityₜ
import LogOS.Domain.UniversalIR.Blum as Blumₜ
import LogOS.Domain.UniversalIR.Size as Sizeₜ

import LogOS.Domain.UniversalIR.Core.All as CoreAllₜ
import LogOS.Domain.UniversalIR.Languages.All as Languagesₜ
import LogOS.Domain.UniversalIR.Examples.All as Examplesₜ
import LogOS.Domain.UniversalIR.While.All as Whileₜ
import LogOS.Domain.UniversalIR.Quantum.All as Quantumₜ
import LogOS.Domain.UniversalIR.Physics.All as Physicsₜ
import LogOS.Domain.UniversalIR.CQM.All as CQMₜ

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
module KernelRichG = KernelRichGₜ
module ObservedKernel = ObservedKernelₜ
module Universality = Universalityₜ
module Blum = Blumₜ
module Size = Sizeₜ

module CoreAll = CoreAllₜ
module Languages = Languagesₜ
module Examples = Examplesₜ
module While = Whileₜ
module Quantum = Quantumₜ
module Physics = Physicsₜ
module CQM = CQMₜ

