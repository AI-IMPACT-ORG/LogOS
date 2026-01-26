{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.UniversalIR.Core where

-- Curated, stable UniversalIR surface.
--
-- Philosophy: `Core` is intentionally *minimal* and namespaced.
--
-- - Use `LogOS.Packs.UniversalIR.All` as the umbrella import.
-- - Use `LogOS.Packs.UniversalIR.Surface` as the “stable lock” entrypoint.
-- - Use `LogOS.Packs.UniversalIR.Applications.*` for story-level wrappers.
--
-- In particular, this module avoids a long list of `open import … public`
-- re-exports. Instead it exposes the Domain components as submodules so the
-- provenance of each definition stays visible.

open import LogOS.Packs.Trust using (PackTrust; stable)

packTrust : PackTrust
packTrust = record { level = stable }

-- Core building blocks (Domain). Keep them namespaced to make the “math objects”
-- pop and to avoid accidental surface drift.
import LogOS.Domain.UniversalIR.IR as IRₜ
import LogOS.Domain.UniversalIR.Encoding as Encodingₜ
import LogOS.Domain.UniversalIR.Backend as Backendₜ
import LogOS.Domain.UniversalIR.Core as Coreₜ
import LogOS.Domain.UniversalIR.Std as Stdₜ
import LogOS.Domain.UniversalIR.Blum as Blumₜ
import LogOS.Domain.UniversalIR.Task as Taskₜ
import LogOS.Domain.UniversalIR.CompilerCorrectness as CompilerCorrectnessₜ
import LogOS.Domain.UniversalIR.Schemes as Schemesₜ
import LogOS.Domain.UniversalIR.Universality as Universalityₜ
import LogOS.Domain.UniversalIR.ArbitraryTasks as ArbitraryTasksₜ
import LogOS.Domain.UniversalIR.TasksToUProcess as TasksToUProcessₜ

module IR = IRₜ
module Encoding = Encodingₜ
module Backend = Backendₜ
module Core = Coreₜ
module Std = Stdₜ
module Blum = Blumₜ
module Task = Taskₜ
module CompilerCorrectness = CompilerCorrectnessₜ
module Schemes = Schemesₜ
module Universality = Universalityₜ
module ArbitraryTasks = ArbitraryTasksₜ
module TasksToUProcess = TasksToUProcessₜ

-- Pack-level refinements.
import LogOS.Packs.UniversalIR.RefinementInitiality as RefinementInitialityₜ
module RefinementInitiality = RefinementInitialityₜ

-- Recommended runner for grade-indexed execution (“machines as schemes”).
open import LogOS.Computation.Scheme public using (run≤; run≤ᵇ)
