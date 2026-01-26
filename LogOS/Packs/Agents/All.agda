{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
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

module AssumptionBundles where
  open import LogOS.Packs.Assumptions.Universality public

module Core where
  open import LogOS.Packs.Agents.Core public

module Lab where
  open import LogOS.Packs.Agents.Lab.All public

module Applications where
  open import LogOS.Packs.Agents.Applications.All public
