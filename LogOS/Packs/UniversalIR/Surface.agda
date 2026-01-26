{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.UniversalIR.Surface where

-- Surface lock for the UniversalIR pack.

open import LogOS.Packs.UniversalIR.All public
-- Keep this as a *namespaced* surface to avoid collisions between the internal
-- module structure of `UniversalIR.Core` and the curated `All` pack surface.
