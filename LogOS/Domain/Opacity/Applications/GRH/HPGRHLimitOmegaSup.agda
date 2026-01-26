{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.Applications.GRH.HPGRHLimitOmegaSup where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Kernel
open import LogOS.Ports.Semantic.SatMor using (SatRefinement₀; sat-→₀)

open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann
open import LogOS.Domain.Opacity.Applications.GRH.HPGRHLimit as HP∞

-- Limit GRH wrapper (legacy “OmegaSup” name).
--
-- This module used to bundle explicit ω-supremum structure as part of the
-- assumptions. The current proof only needs the finite regulator operator facts
-- (Opᵢ-fixed) plus a limit-level spectral clause (Op∞-fixed ⇒ OnLine), so the
-- ω-sup fields have been removed to keep the dependency graph honest.

record HP∞OmegaSupAssumptions {ℓ}
                            {Sig : LogOSSignature ℓ}
                            {Q   : QAdapter ℓ}
                            (K   : Kernel Sig Q)
                            (AHP : HP∞.ApproxHP Sig Q K)
                            (RS  : RiemannSpectral)
                            : Set (lsuc ℓ) where
  open Kernel K
  open RiemannSpectral RS

  field
    -- Spectral adapter to boundary constraints
    c : Spectral → ConPreorder.Con (BulkBoundary.bnd BB)

    -- Chosen finite regulator index (to seed the limit lifting)
    i₀ : HP∞.ResIdx.I (HP∞.ApproxHP.idx AHP)

    -- Finite regulator operator fact at the chosen index.
    fixed₀-ref : SatRefinement₀ Spectral
                  (λ _ s → NontrivialZero s)
                  (λ _ s → HP∞.ApproxHP.Opᵢ AHP i₀ (HP∞.ApproxHP.embedᵢ AHP i₀ (c s))
                            ≡ HP∞.ApproxHP.embedᵢ AHP i₀ (c s))

    -- Limit spectral clause: Op∞-fixed implies OnLine (refinement form).
    opFixed-ref : SatRefinement₀ Spectral
                   (λ _ s → HP∞.ApproxHP.Op∞ AHP (HP∞.ApproxHP.embed∞ AHP (c s))
                             ≡ HP∞.ApproxHP.embed∞ AHP (c s))
                   (λ _ s → OnLine s)

  OpᵢFixedAtZero : ∀ s → NontrivialZero s →
    HP∞.ApproxHP.Opᵢ AHP i₀ (HP∞.ApproxHP.embedᵢ AHP i₀ (c s))
      ≡ HP∞.ApproxHP.embedᵢ AHP i₀ (c s)
  OpᵢFixedAtZero s nz = sat-→₀ fixed₀-ref s nz

  Op∞Fixed→OnLine : ∀ s →
    HP∞.ApproxHP.Op∞ AHP (HP∞.ApproxHP.embed∞ AHP (c s))
      ≡ HP∞.ApproxHP.embed∞ AHP (c s)
    → OnLine s
  Op∞Fixed→OnLine s fixed = sat-→₀ opFixed-ref s fixed

-- Theorem: from finite regulator operator facts + a limit spectral clause,
-- derive GRH_Without_Vacuity_Guards.

GRH_Without_Vacuity_Guards_via_HP∞_OmegaSup
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K   : Kernel Sig Q)
    (AHP : HP∞.ApproxHP Sig Q K)
    (RS  : RiemannSpectral)
    (AC  : HP∞OmegaSupAssumptions K AHP RS)
  → ∀ s → RiemannSpectral.NontrivialZero RS s → RiemannSpectral.OnLine RS s
GRH_Without_Vacuity_Guards_via_HP∞_OmegaSup K AHP RS AC s nz =
  let fixed∞ =
        HP∞.derive-Op∞Fixed-at K AHP RS
          (HP∞OmegaSupAssumptions.c AC)
          (HP∞OmegaSupAssumptions.i₀ AC)
          (HP∞OmegaSupAssumptions.OpᵢFixedAtZero AC)
          s nz
  in HP∞OmegaSupAssumptions.Op∞Fixed→OnLine AC s fixed∞
