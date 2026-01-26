{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Applications.Networks where

-- Curated “agent networks” application surface:
-- heterogeneous wiring + port-level interoperability + network-as-agent wrappers.

module Core where
  open import LogOS.Packs.Agents.Networks.Core public

module Hetero where
  open import LogOS.Packs.Agents.Networks.Hetero public

module Interop where
  open import LogOS.Packs.Agents.Networks.Interop public

module MonitorInterop where
  open import LogOS.Packs.Agents.Networks.MonitorInterop public

module NetworkAgent where
  open import LogOS.Packs.Agents.Networks.NetworkAgent public

