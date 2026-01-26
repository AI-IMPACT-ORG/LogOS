{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Applications.All where

-- Curated “application” entrypoints for the Agents storyline.
--
-- The stable Agents pack is mostly a navigation layer over kernel-level
-- structure; this namespace provides a single predictable place to look for the
-- most application-facing surfaces (sockets, networks, frameworks).

module Socket where
  open import LogOS.Packs.Agents.Applications.Socket public

module Networks where
  open import LogOS.Packs.Agents.Applications.Networks public

module Frameworks where
  open import LogOS.Packs.Agents.Applications.Frameworks public

