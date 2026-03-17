{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Ports where

-- Ports (hexagonal boundary interfaces).
--
-- The port implementations live under `LogOS/Ports/**` and must not depend on
-- `LogOS/Adapters/**` or `LogOS/Apps/**` (hexagonal discipline).
--
-- This module provides curated port surfaces (re-exports).
-- Heavier optional physical doctrine packs live under
-- `LogOS.API.Ports.PhysicalOptional` and are not re-exported here.

open import LogOS.API.Ports.Physical public
open import LogOS.API.Ports.UniversalityArchitecture public
import LogOS.API.Ports.UniversalityLOG
open import LogOS.API.Ports.Valuation public
open import LogOS.API.Ports.LTDecorations public

module UniversalityLOG = LogOS.API.Ports.UniversalityLOG

-- Quarantine bridge (typecheck-only, non-public):
-- keep quarantined meaning-changing constructions reachable without exposing
-- them on the curated API surface.
private
  open import LogOS.Ports.Bridges.Quarantine using (quarantine-ok)

  quarantine-ok-used = quarantine-ok
