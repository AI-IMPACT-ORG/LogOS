{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Assumptions where

-- Core-only entrypoint: shared logic core used by assumption bundles.
--
-- Domain bundles live under `LogOS.Packs.Assumptions.*` to keep the API layer
-- independent of application developments (import-layer discipline).
--
-- This surface is for:
-- - the core assumption bundle machinery (no domain/application claims)
--
-- Not for:
-- - application-specific assumption ledgers (use `LogOS.Packs.*` or `LogOS.Domain.*`)

open import LogOS.API.Assumptions.Core public
