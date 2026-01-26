{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.Applications.GRH.ZetaBridge where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Kernel
open import LogOS.Ports.Semantic.SatMor using (SatRefinement; SatRefinement₀; composeSatRefinement; sat-→₀)

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
    c : Spectral → ConPreorder.Con (BulkBoundary.bnd BB)
    zero-ref : SatRefinement₀ Spectral
                (λ _ s → NontrivialZero s)
                (λ _ s → Op (embed (c s)) ≡ embed (c s))

    opFixed-ref : SatRefinement₀ Spectral
                   (λ _ s → Op (embed (c s)) ≡ embed (c s))
                   (λ _ s → OnLine s)

  zero→OpFixed : ∀ s → NontrivialZero s → Op (embed (c s)) ≡ embed (c s)
  zero→OpFixed s nz = sat-→₀ zero-ref s nz

  opFixed→OnLine : ∀ s → Op (embed (c s)) ≡ embed (c s) → OnLine s
  opFixed→OnLine s fixed = sat-→₀ opFixed-ref s fixed

  zero→OnLine : ∀ s → NontrivialZero s → OnLine s
  zero→OnLine s nz = sat-→₀ (composeSatRefinement zero-ref opFixed-ref) s nz

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
  ; zero-ref =
      record
        { sat-→ = λ _ s nz → ZetaOpBridgeFinite.zero→OpFixed B s nz
        }
  ; opFixed-ref =
      record
        { sat-→ = λ _ s fixed → ZetaOpBridgeFinite.opFixed→OnLine B s fixed
        }
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
    c : Spectral → ConPreorder.Con (BulkBoundary.bnd BB)
    zero-ref : SatRefinement (HPLimit.ResIdx.I (HPLimit.ApproxHP.idx AHP)) Spectral
                (λ _ s → NontrivialZero s)
                (λ i s →
                  HPLimit.ApproxHP.Opᵢ AHP i (HPLimit.ApproxHP.embedᵢ AHP i (c s))
                    ≡ HPLimit.ApproxHP.embedᵢ AHP i (c s))

    opFixed-ref : SatRefinement₀ Spectral
                   (λ _ s →
                      HPLimit.ApproxHP.Op∞ AHP (HPLimit.ApproxHP.embed∞ AHP (c s))
                        ≡ HPLimit.ApproxHP.embed∞ AHP (c s))
                   (λ _ s → OnLine s)

  zero→OpᵢFixed : ∀ i s → NontrivialZero s →
    HPLimit.ApproxHP.Opᵢ AHP i (HPLimit.ApproxHP.embedᵢ AHP i (c s))
      ≡ HPLimit.ApproxHP.embedᵢ AHP i (c s)
  zero→OpᵢFixed i s nz = SatRefinement.sat-→ zero-ref i s nz

  op∞Fixed→OnLine : ∀ s →
    HPLimit.ApproxHP.Op∞ AHP (HPLimit.ApproxHP.embed∞ AHP (c s))
      ≡ HPLimit.ApproxHP.embed∞ AHP (c s)
    → OnLine s
  op∞Fixed→OnLine s fixed = sat-→₀ opFixed-ref s fixed

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
  ; zero-ref =
      record
        { sat-→ = λ _ s nz →
            HPLimit.derive-Op∞Fixed K AHP RS (ZetaOpBridgeLimit.c B) i
              (ZetaOpBridgeLimit.zero→OpᵢFixed B) s nz
        }
  ; opFixed-ref =
      record
        { sat-→ = λ _ s fixed → ZetaOpBridgeLimit.op∞Fixed→OnLine B s fixed
        }
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
