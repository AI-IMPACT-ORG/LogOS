{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.All where

-- Experimental surface: stable agents pack plus transformer/scaling and
-- complexity-linked physics/RG-flow extensions.

open import LogOS.Packs.Trust using (PackTrust; experimental)

packTrust : PackTrust
packTrust = record { level = experimental }

-- Re-export the stable lab surface, then add experimental extensions.
import LogOS.Packs.Agents.Lab.All as Lab

import LogOS.Packs.Agents.Applications.All as Applications

module AssumptionBundles where
  open import LogOS.Packs.Assumptions.Universality public
  open import LogOS.Packs.Assumptions.Physics public

import LogOS.Packs.Agents.Experimental.Lab as Experimental
