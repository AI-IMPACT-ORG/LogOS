{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
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
import LogOS.UniversalIR.IR as IRₜ
import LogOS.UniversalIR.Encoding as Encodingₜ
import LogOS.UniversalIR.Backend as Backendₜ
import LogOS.UniversalIR.Core as Coreₜ
import LogOS.UniversalIR.Std as Stdₜ
import LogOS.UniversalIR.Blum as Blumₜ
import LogOS.UniversalIR.Task as Taskₜ
import LogOS.UniversalIR.CompilerCorrectness as CompilerCorrectnessₜ
import LogOS.UniversalIR.Schemes as Schemesₜ
import LogOS.UniversalIR.Universality as Universalityₜ
import LogOS.UniversalIR.ArbitraryTasks as ArbitraryTasksₜ
import LogOS.UniversalIR.TasksToUProcess as TasksToUProcessₜ

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
