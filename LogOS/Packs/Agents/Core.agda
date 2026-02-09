{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Core where

-- Curated, stable Agents “core surface” (no demos).
--
-- Philosophy: `Core` is intentionally *minimal* and namespaced.
-- - Use `LogOS.Packs.Agents.All` as the umbrella import.
-- - Use `LogOS.Packs.Agents.Surface` as the “stable lock” entrypoint.
-- - Use `LogOS.Packs.Agents.Applications.*` for story-level wrappers.

open import LogOS.Packs.Trust using (PackTrust; stable)

packTrust : PackTrust
packTrust = record { level = stable }

-- Core building blocks. Keep them namespaced so the provenance of each concept
-- is explicit (socket vs learning vs networks vs frameworks).
import LogOS.Packs.Agents.Socket.Core     as Socketₜ
import LogOS.Packs.Agents.Learning.Core   as Learningₜ
import LogOS.Packs.Agents.Networks.Core   as Networksₜ
import LogOS.Packs.Agents.Frameworks.Core as Frameworksₜ
import LogOS.Packs.Agents.Lab.Core        as Labₜ

module Socket     = Socketₜ
module Learning   = Learningₜ
module Networks   = Networksₜ
module Frameworks = Frameworksₜ
module Lab        = Labₜ

