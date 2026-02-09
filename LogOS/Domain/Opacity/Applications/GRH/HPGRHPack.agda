{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.Applications.GRH.HPGRHPack where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Kernel
open import LogOS.Ports.Semantic.SatMor using (SatRefinement₀; composeSatRefinement; sat-→₀)

open import LogOS.Domain.Opacity.NumberTheory.HP.Interface as HPi

open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann

-- Assumptions to derive a boundary GRH via Hilbert–Pólya

record HPGRHAssumptions {ℓ}
                        (Sig : LogOSSignature ℓ)
                        (Q   : QAdapter ℓ)
                        (K   : Kernel Sig Q)
                        (HP  : HPi.HPInterface K)
                        (EF  : HPi.EmbedFaithful K HP)
                        (RS  : RiemannSpectral)
                        : Set (lsuc ℓ) where
  open Kernel K
  open RiemannSpectral RS
  open HPi.HPInterface HP
  field
    -- Interpret spectral points as boundary constraints
    c : Spectral → ConPreorder.Con (BulkBoundary.bnd BB)

    -- Nontrivial zeros are Op-fixed via embed ∘ c (refinement form).
    zero-ref : SatRefinement₀ Spectral
                (λ _ s → NontrivialZero s)
                (λ _ s → Op (embed (c s)) ≡ embed (c s))

    -- Op-fixed implies OnLine (model-local spectral claim, refinement form).
    opFixed-ref : SatRefinement₀ Spectral
                   (λ _ s → Op (embed (c s)) ≡ embed (c s))
                   (λ _ s → OnLine s)

  OpFixedOnZero : ∀ s → NontrivialZero s → Op (embed (c s)) ≡ embed (c s)
  OpFixedOnZero s nz = sat-→₀ zero-ref s nz

  OpFixed→OnLine : ∀ s → Op (embed (c s)) ≡ embed (c s) → OnLine s
  OpFixed→OnLine s fixed = sat-→₀ opFixed-ref s fixed

  zero→OnLine : ∀ s → NontrivialZero s → OnLine s
  zero→OnLine s nz = sat-→₀ (composeSatRefinement zero-ref opFixed-ref) s nz

-- Theorem: GRH_Without_Vacuity_Guards at the boundary from HP + assumptions

GRH_Without_Vacuity_Guards_via_HP
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K   : Kernel Sig Q)
    (HP  : HPi.HPInterface K)
    (EF  : HPi.EmbedFaithful K HP)
    (RS  : RiemannSpectral)
    (A   : HPGRHAssumptions Sig Q K HP EF RS)
  → ∀ s → RiemannSpectral.NontrivialZero RS s → RiemannSpectral.OnLine RS s
GRH_Without_Vacuity_Guards_via_HP K HP EF RS A s nz =
  HPGRHAssumptions.zero→OnLine A s nz
