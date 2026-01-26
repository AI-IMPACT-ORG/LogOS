{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.Applications.GRH.DiagonalNTemplate where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel
open import LogOS.Domain.Opacity.NumberTheory.HP.Interface as HPi
open import LogOS.Domain.Opacity.NumberTheory.HP.Flow as HP

open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann
open import LogOS.Domain.Opacity.NumberTheory.LFunction.DiagonalTX
open import LogOS.Domain.Opacity.Applications.GRH.DiagonalToHPBridge
open import LogOS.Domain.Opacity.Applications.GRH.ZetaBridge

-- Minimal N-factor template (no stdlib lists):
-- Provide your own finite index type P and local diagonal predicate a₁ : P → Spectral → Set.

record DiagonalNPack {ℓ ℓTX}
                     {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                     (K   : Kernel Sig Q)
                     (HP  : HPi.HPInterface K)
                     (RS  : RiemannSpectral)
                     : Set (lsuc (ℓ ⊔ ℓTX)) where
  field
    TX   : DiagonalTX {ℓTX} RS
    Sel  : DiagHPSelector {ℓ} {ℓTX} K HP RS TX

-- One-liner GRH from the N-factor diagonal pack

GRH_Without_Vacuity_Guards_from_diagonalN
  : ∀ {ℓ ℓTX} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K   : Kernel Sig Q)
    (HP  : HPi.HPInterface K)
    (EF  : HPi.EmbedFaithful K HP)
    (RS  : RiemannSpectral)
    (P   : DiagonalNPack {ℓ} {ℓTX} K HP RS)
  → ∀ s → RiemannSpectral.NontrivialZero RS s → RiemannSpectral.OnLine RS s
GRH_Without_Vacuity_Guards_from_diagonalN K HP EF RS P =
  let open DiagonalNPack P in
  GRH_Without_Vacuity_Guards_from_finite K HP EF RS (fromDiagonal K HP RS TX Sel)
