{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Surface where

-- Surface lock for the stable Agents storyline.

open import LogOS.Packs.Agents.All public
-- Keep this surface namespaced via `All` to avoid collisions with core tier names
-- (e.g. `S`) and to keep the Agents public surface stable.
