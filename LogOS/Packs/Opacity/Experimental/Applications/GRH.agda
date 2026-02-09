{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Opacity.Experimental.Applications.GRH where

-- Curated surface: Opacity infrastructure + GRH/RH *proof templates*.
--
-- Intellectual-honesty note:
-- this is not a classical analytic proof of GRH/RH. The library treats GRH/RH
-- as an *axiom ledger* / *reverse-mathematics template* that isolates which
-- interfaces and guards would suffice to derive a GRH-shaped statement.

open import LogOS.Packs.Opacity.Experimental.Core public

-- Guarded surface: packaged GRH claim object together with explicit vacuity guards.
module Guarded where
  open import LogOS.Domain.Opacity.GRHLedger public

-- Guardless surface: raw theorems that conclude `GRH_Without_Vacuity_Guards ...`
-- (explicitly named as such). These are useful internally, but should be used
-- with explicit vacuity guards when exporting a public “GRH claim”.
module Guardless where
  open import LogOS.Domain.Opacity.Applications.GRH.All public

  module ZFC where
    open import LogOS.Prelude using (Level)
    open import LogOS.Base.Signature using (LogOSSignature)
    open import LogOS.Minimal.Adapter using (QAdapter)
    open import LogOS.Kernel using (Kernel)
    open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann using (RiemannSpectral)
    import LogOS.Packs.Assumptions.ZFC as AssumpZFC

    zfBundleFromStability
      : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
        {K : Kernel Sig Q} {RS : RiemannSpectral}
        (Stab : ZFCBridge.ZFCFlowStability {ℓ} {Sig} {Q} K RS)
      → AssumpZFC.ZFBundle (ZFCBridge.ZFCFlowStability.coreLK Stab)
    zfBundleFromStability Stab = record { zf = ZFCBridge.ZFCFlowStability.zf Stab }
