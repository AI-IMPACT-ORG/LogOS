{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Networks.Safety where

open import LogOS.Prelude

-- Network-level safety results are expressed by composing boundary endomaps
-- (monitors) and transporting them along ports/adapters.
--
-- This module currently re-exports the monitor interface; concrete theorems are
-- intended to be instantiated per model/network wiring.

open import LogOS.Packs.Agents.Safety.Monitor public

