{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Surface where

-- Surface lock for the experimental Agents storyline.

open import LogOS.Packs.Agents.Experimental.All public
-- Keep this surface namespaced via `All` to avoid collisions with core tier names
-- (e.g. `S`) and to keep the public surface stable.
