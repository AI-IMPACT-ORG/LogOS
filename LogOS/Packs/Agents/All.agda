{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.All where

-- Stable lab surface (socket + learning + networks + frameworks).
-- Experimental extensions live under `LogOS.Packs.Agents.Experimental.All`.

open import LogOS.Packs.Trust using (PackTrust; stable)

packTrust : PackTrust
packTrust = record { level = stable }

open import LogOS.Packs.Agents.Lab.All public
