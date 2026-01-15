{-
LogOS: an Agda research library for foundational logic system architecture.
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

open import LogOS.Packs.Agents.All public hiding (packTrust)

module Experimental where
  open import LogOS.Packs.Agents.Experimental.Lab public
