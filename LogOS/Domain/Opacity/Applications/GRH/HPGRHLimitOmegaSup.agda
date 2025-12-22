{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.Applications.GRH.HPGRHLimitOmegaSup where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel
open import LogOS.Axioms.OmegaSup.Interface as OmegaSup

open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann
open import LogOS.Domain.Opacity.Applications.GRH.HPGRHLimit as HP∞

-- ω-supremum-flavored limit GRH wrapper (explicit ω-sup assumption)
--
-- Idea: build an OmegaCPO for the boundary poset using an explicit ω-supremum
-- operator (ChainSup), assume a FiniteFirst witness (cont-ω) for the model’s
-- Flow, and combine with an ApproxHP family to conclude GRH from finite
-- regulator operator facts.

record HP∞OmegaSupAssumptions {ℓ}
                            {Sig : LogOSSignature ℓ}
                            {Q   : QAdapter ℓ}
                            (K   : Kernel Sig Q)
                            (AHP : HP∞.ApproxHP Sig Q K)
                            (RS  : RiemannSpectral)
                            : Set (lsuc ℓ) where
  open Kernel K
  open RiemannSpectral RS
  module Gd = Truth.GuardedTruth Sig Q

  field
    -- Bottom element and its property, to seed OmegaCPO via ω-sup selection
    bot   : ConPoset.Con (BulkBoundary.bnd BB)
    isBot : ∀ c → ConPoset._⊑_ (BulkBoundary.bnd BB) bot c

    -- Explicit ω-supremum operator (no global postulate import).
    CS : OmegaSup.ChainSup (BulkBoundary.bnd BB)

    -- Finite-first/continuity witness on the boundary poset using the ChainSup-built OmegaCPO
    FF : Gd.FiniteFirst (BulkBoundary.bnd BB)
                         (GTruth)
                         (OmegaSup.omegaCPO-from-chainSup Sig Q (BulkBoundary.bnd BB) bot isBot CS)

    -- Spectral adapter to boundary constraints
    c : Spectral → ConPoset.Con (BulkBoundary.bnd BB)

    -- Chosen finite regulator index (to seed the limit lifting)
    i₀ : HP∞.ResIdx.I (HP∞.ApproxHP.idx AHP)

    -- Finite regulator operator facts: every nontrivial zero maps to an Opᵢ-fixed point
    allFixedFinite : ∀ i s → NontrivialZero s →
      HP∞.ApproxHP.Opᵢ AHP i (HP∞.ApproxHP.embedᵢ AHP i (c s))
        ≡ HP∞.ApproxHP.embedᵢ AHP i (c s)

    -- Limit spectral clause: Op∞-fixed implies OnLine
    Op∞Fixed→OnLine : ∀ s →
      HP∞.ApproxHP.Op∞ AHP (HP∞.ApproxHP.embed∞ AHP (c s))
        ≡ HP∞.ApproxHP.embed∞ AHP (c s)
      → OnLine s

-- Theorem: from ω-sup selector-built OmegaCPO + finite regulator operator facts + limit spectral clause,
-- derive GRH_Without_Vacuity_Guards

GRH_Without_Vacuity_Guards_via_HP∞_OmegaSup
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K   : Kernel Sig Q)
    (AHP : HP∞.ApproxHP Sig Q K)
    (RS  : RiemannSpectral)
    (AC  : HP∞OmegaSupAssumptions K AHP RS)
  → ∀ s → RiemannSpectral.NontrivialZero RS s → RiemannSpectral.OnLine RS s
GRH_Without_Vacuity_Guards_via_HP∞_OmegaSup K AHP RS AC s nz =
  let fixed∞ =
        HP∞.derive-Op∞Fixed K AHP RS
          (HP∞OmegaSupAssumptions.c AC)
          (HP∞OmegaSupAssumptions.i₀ AC)
          (HP∞OmegaSupAssumptions.allFixedFinite AC)
          s nz
  in HP∞OmegaSupAssumptions.Op∞Fixed→OnLine AC s fixed∞
