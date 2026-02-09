{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.TelemetryInvariant where

-- Telemetry invariance: observationally equivalent boundary programs yield
-- trace-equivalent telemetry (observation-only stability).

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.World
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Boundary.IO
open import LogOS.Boundary.Telemetry

telemetry-indistinguishable
  : ∀ {ℓ ℓT}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    {B : BoundaryIO Sig Q W BB H}
    {T : TelemetryTrace ℓT}
  → (obs : LogOSSignature.∂Cosp Sig → TelemetryTrace.Trace T)
  → MonoMap (ObsCospPreorder B) (TelemetryTrace.trace T) obs
  → {p q : LogOSSignature.∂Cosp Sig}
  → p ≈∂Cosp[ B ] q
  → Trace≈ T (obs p) (obs q)
telemetry-indistinguishable {B = B} {T = T} obs mono {p} {q} eq =
  observe-∂-respects-from-mono {B = B} {T = T} obs mono {p = p} {q = q} eq
