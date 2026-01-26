{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.Applications.GRH.ZetaHPIdentification where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel
open import LogOS.Kernel.Endo

open import LogOS.Domain.Opacity.NumberTheory.HP.Interface as HPi
import LogOS.Domain.Opacity.NumberTheory.HP.Flow as HPFlow

open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann
open import LogOS.Domain.Opacity.NumberTheory.LFunction.RiemannFacts using (RiemannFacts; RiemannSpectralFromFacts)
open import LogOS.Domain.Opacity.Applications.GRH.ZetaBridge

-- A precise “ζ ↔ Hilbert–Pólya” bridge statement:
--
-- If a model supplies (i) an HP evolution operator intertwining the kernel’s
-- boundary Flow and (ii) a ζ-facing selector `c` such that every nontrivial zero
-- yields an Op-fixed witness at `embed (c s)`, then (with faithfulness) each
-- nontrivial zero yields a genuine Flow-fixed boundary constraint.

NontrivialZero→FlowFixed
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K   : Kernel Sig Q)
    (HP  : HPi.HPInterface K)
    (EF  : HPi.EmbedFaithful K HP)
    (RS  : RiemannSpectral)
    (B   : ZetaOpBridgeFinite Sig Q K HP RS)
  → ∀ s → RiemannSpectral.NontrivialZero RS s
        → Endo.fn (Flow-Endo K) (ZetaOpBridgeFinite.c B s)
          ≡ ZetaOpBridgeFinite.c B s
NontrivialZero→FlowFixed K HP EF RS B s nz =
  HPFlow.Op-fixed→Flow-fixed K HP EF (ZetaOpBridgeFinite.c B s)
    (ZetaOpBridgeFinite.zero→OpFixed B s nz)

-- Same theorem, but phrased in the textbook-aligned ζ/ξ facts interface.
-- This makes explicit that “nontrivial zero” is a completed-ξ zero in the strip.

NontrivialXiZero→FlowFixed
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K   : Kernel Sig Q)
    (HP  : HPi.HPInterface K)
    (EF  : HPi.EmbedFaithful K HP)
    (F   : RiemannFacts)
    (B   : ZetaOpBridgeFinite Sig Q K HP (RiemannSpectralFromFacts F))
  → ∀ s → (RiemannFacts.XiZero F s × RiemannFacts.InStrip F s)
        → Endo.fn (Flow-Endo K) (ZetaOpBridgeFinite.c B s)
          ≡ ZetaOpBridgeFinite.c B s
NontrivialXiZero→FlowFixed K HP EF F B s nz =
  NontrivialZero→FlowFixed K HP EF (RiemannSpectralFromFacts F) B s nz
