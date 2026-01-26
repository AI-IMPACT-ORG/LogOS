{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Opacity.Experimental.Surface where

-- Surface lock for the experimental opacity / observability storyline.

open import LogOS.Packs.Opacity.Experimental.All public
-- Keep this surface namespaced via `All` to avoid collisions between the pack
-- skeleton modules and the domain ledger modules.
