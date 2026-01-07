{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Opacity.Surface where

-- Surface lock for the opacity / observability storyline.

open import LogOS.Packs.Opacity.All public
-- Keep this surface namespaced via `All` to avoid collisions between the pack
-- skeleton modules and the domain ledger modules.
