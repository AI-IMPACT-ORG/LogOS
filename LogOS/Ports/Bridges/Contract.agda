{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Bridges.Contract where

-- Bridge contract template (explicit meaning-change import point).
--
-- The human intent of a bridge must be documented in the bridge module header
-- (enforced by CI). This file provides a minimal type-level shape for the
-- “source boundary → target boundary” part.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; MonoMap; idMonoMap)
open import LogOS.LT.ConPreorder.Unit using (UnitPreorder)

-- Minimal dummy boundary for “witness-only” bridges that do not expose any
-- boundary translation yet.
UnitBoundary : ConPreorder lzero lzero
UnitBoundary = UnitPreorder

record BridgeContract
  {ℓSrcCon ℓSrcRel ℓTgtCon ℓTgtRel : Level}
  (Src : ConPreorder ℓSrcCon ℓSrcRel)
  (Tgt : ConPreorder ℓTgtCon ℓTgtRel)
  : Set (lsuc (ℓSrcCon ⊔ ℓSrcRel ⊔ ℓTgtCon ⊔ ℓTgtRel)) where
  field
    map  : Con Src → Con Tgt
    mono : MonoMap Src Tgt map

open BridgeContract public
idBridgeContract
  : ∀ {ℓCon ℓRel} {CP : ConPreorder ℓCon ℓRel}
  → BridgeContract CP CP
idBridgeContract {CP = CP} =
  record
    { map  = λ x → x
    ; mono = idMonoMap {CP = CP}
    }
