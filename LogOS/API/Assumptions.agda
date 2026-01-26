{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Assumptions where

-- Core-only entrypoint: shared logic core used by assumption bundles.
--
-- Domain bundles live under `LogOS.Packs.Assumptions.*` to keep the API layer
-- independent of application developments (import-layer discipline).

open import LogOS.API.Assumptions.Core public
