{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.Applications.GRH.ZetaBridge where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Kernel

open import LogOS.Domain.Opacity.NumberTheory.HP.Interface as HPi
open import LogOS.Domain.Opacity.NumberTheory.HP.Flow as HP

open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann
open import LogOS.Domain.Opacity.NumberTheory.LFunction.RiemannFacts
open import LogOS.Domain.Opacity.Applications.GRH.HPGRHPack as HPFinite
open import LogOS.Domain.Opacity.Applications.GRH.HPGRHLimit as HPLimit

-- Finite HP bridge: package the two operator-level witnesses needed by HPGRHPack

record ZetaOpBridgeFinite {ℓ}
                         (Sig : LogOSSignature ℓ)
                         (Q   : QAdapter ℓ)
                         (K   : Kernel Sig Q)
                         (HP  : HPi.HPInterface K)
                         (RS  : RiemannSpectral)
                         : Set (lsuc ℓ) where
  open Kernel K
  open RiemannSpectral RS
  open HPi.HPInterface HP
  field
    c : Spectral → ConPoset.Con (BulkBoundary.bnd BB)
    zero→OpFixed : ∀ s → NontrivialZero s →
      Op (embed (c s)) ≡ embed (c s)
    opFixed→OnLine : ∀ s →
      Op (embed (c s)) ≡ embed (c s)
      → OnLine s

mkHPAssumptions
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K   : Kernel Sig Q)
    (HP  : HPi.HPInterface K)
    (EF  : HPi.EmbedFaithful K HP)
    (RS  : RiemannSpectral)
    (B   : ZetaOpBridgeFinite Sig Q K HP RS)
  → HPFinite.HPGRHAssumptions Sig Q K HP EF RS
mkHPAssumptions K HP EF RS B = record
  { c = ZetaOpBridgeFinite.c B
  ; OpFixedOnZero = ZetaOpBridgeFinite.zero→OpFixed B
  ; OpFixed→OnLine = ZetaOpBridgeFinite.opFixed→OnLine B
  }

GRH_Without_Vacuity_Guards_from_finite
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K   : Kernel Sig Q)
    (HP  : HPi.HPInterface K)
    (EF  : HPi.EmbedFaithful K HP)
    (RS  : RiemannSpectral)
    (B   : ZetaOpBridgeFinite Sig Q K HP RS)
  → ∀ s → RiemannSpectral.NontrivialZero RS s → RiemannSpectral.OnLine RS s
GRH_Without_Vacuity_Guards_from_finite K HP EF RS B =
  HPFinite.GRH_Without_Vacuity_Guards_via_HP K HP EF RS (mkHPAssumptions K HP EF RS B)

-- Limit HP bridge: package finite regulator witnesses and a limit spectral clause

record ZetaOpBridgeLimit {ℓ}
                        (Sig : LogOSSignature ℓ)
                        (Q   : QAdapter ℓ)
                        (K   : Kernel Sig Q)
                        (AHP : HPLimit.ApproxHP Sig Q K)
                        (RS  : RiemannSpectral)
                        : Set (lsuc ℓ) where
  open Kernel K
  open RiemannSpectral RS
  field
    c : Spectral → ConPoset.Con (BulkBoundary.bnd BB)
    zero→OpᵢFixed : ∀ i s → NontrivialZero s →
      HPLimit.ApproxHP.Opᵢ AHP i (HPLimit.ApproxHP.embedᵢ AHP i (c s))
        ≡ HPLimit.ApproxHP.embedᵢ AHP i (c s)
    op∞Fixed→OnLine : ∀ s →
      HPLimit.ApproxHP.Op∞ AHP (HPLimit.ApproxHP.embed∞ AHP (c s))
        ≡ HPLimit.ApproxHP.embed∞ AHP (c s)
      → OnLine s

mkHP∞Assumptions
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K   : Kernel Sig Q)
    (AHP : HPLimit.ApproxHP Sig Q K)
    (RS  : RiemannSpectral)
    (B   : ZetaOpBridgeLimit Sig Q K AHP RS)
    (i   : HPLimit.ResIdx.I (HPLimit.ApproxHP.idx AHP))
  → HPLimit.HP∞GRHAssumptions K AHP RS
mkHP∞Assumptions K AHP RS B i = record
  { c = ZetaOpBridgeLimit.c B
  ; Op∞FixedOnZero = λ s nz →
      HPLimit.derive-Op∞Fixed K AHP RS (ZetaOpBridgeLimit.c B) i (ZetaOpBridgeLimit.zero→OpᵢFixed B) s nz
  ; Op∞Fixed→OnLine = ZetaOpBridgeLimit.op∞Fixed→OnLine B
  }

GRH_Without_Vacuity_Guards_from_limit
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K   : Kernel Sig Q)
    (AHP : HPLimit.ApproxHP Sig Q K)
    (RS  : RiemannSpectral)
    (B   : ZetaOpBridgeLimit Sig Q K AHP RS)
    (i   : HPLimit.ResIdx.I (HPLimit.ApproxHP.idx AHP))
  → ∀ s → RiemannSpectral.NontrivialZero RS s → RiemannSpectral.OnLine RS s
GRH_Without_Vacuity_Guards_from_limit K AHP RS B i =
  HPLimit.GRH_Without_Vacuity_Guards_via_HP∞ K AHP RS (mkHP∞Assumptions K AHP RS B i)
