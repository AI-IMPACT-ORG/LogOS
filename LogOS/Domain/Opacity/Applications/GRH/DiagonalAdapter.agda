{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.Applications.GRH.DiagonalAdapter where

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

-- One-line wrapper: build the finite HP bridge from a diagonal truncated operator
-- specification and derive the GRH-style conclusion.

GRH_Without_Vacuity_Guards_from_diagonal
  : ∀ {ℓ ℓTX}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K   : Kernel Sig Q)
    (HP  : HPi.HPInterface K)
    (EF  : HPi.EmbedFaithful K HP)
    (RS  : RiemannSpectral)
    (TX  : DiagonalTX {ℓTX} RS)
    (Sel : DiagHPSelector {ℓ} {ℓTX} K HP RS TX)
  → ∀ s → RiemannSpectral.NontrivialZero RS s → RiemannSpectral.OnLine RS s
GRH_Without_Vacuity_Guards_from_diagonal K HP EF RS TX Sel =
  let Bf = fromDiagonal K HP RS TX Sel in
  GRH_Without_Vacuity_Guards_from_finite K HP EF RS Bf
