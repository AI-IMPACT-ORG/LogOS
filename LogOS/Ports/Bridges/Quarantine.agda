{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Bridges.Quarantine where

-- Curated bridge into quarantined meaning-changing constructions.
--
-- This module is the *only* intended import point for quarantined ports from
-- the normal codebase. Keep exports small and explicit.
--
-- BRIDGE-CONTRACT
-- Source boundary: UnitBoundary (witness-only)
-- Target boundary: UnitBoundary (witness-only)
-- Intent: expose a single harmless witness (`quarantine-ok`) so the quarantine zone
--   stays reachable/typechecked, without exporting any meaning-changing API.
-- Why allowed: does not export any boundary translation or non-pointwise meaning
--   change; it only re-exports `⊤`.

open import LogOS.Prelude using (⊤)
open import LogOS.Ports.Bridges.Contract using (UnitBoundary; BridgeContract; idBridgeContract)
open import LogOS.Ports.Quarantine.Core using (ok)

bridgeContract : BridgeContract UnitBoundary UnitBoundary
bridgeContract = idBridgeContract

-- Re-export only a harmless witness for now.
quarantine-ok : ⊤
quarantine-ok = ok
