{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.Legacy.ZetaAccessibleMeetLimitLedger where

-- Legacy: superseded by the stable meet-limit ledger.

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

open import LogOS.Domain.Opacity.NumberTheory.LFunction.RiemannFacts using (RiemannFacts; RiemannSpectralFromFacts; Partition≡DS)
open import LogOS.Domain.Opacity.NumberTheory.LFunction.PartitionZetaBridge as PZ
open import LogOS.Domain.Opacity.NumberTheory.LFunction.ZerosPack using (GRH_Without_Vacuity_Guards)

import LogOS.Domain.Opacity.Legacy.AccessibleWeilMeetLimitBridge as AWLM
import LogOS.Theorems.Meta.QuartetCore as Quartet

-- A compact, ζ-facing wrapper for the “accessible Weil + meet-limit” route:
-- instantiate the bridge at `RS = RiemannSpectralFromFacts F`, and derive
-- GRH_Without_Vacuity_Guards.
--
-- This keeps ζ semantics (Dirichlet-series and/or partition-first) separate from
-- the observer/logic machinery: the only bridge input is a meet-limit regulator pack.

record ZetaAccessibleMeetLimitLedger {ℓ ℓW ℓC : Level}
                                     {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                                     (K : Kernel Sig Q)
                                     (F : RiemannFacts)
                                     : Set (lsuc (ℓ ⊔ ℓW ⊔ lsuc ℓC)) where
  private
    RS = RiemannSpectralFromFacts F

  field
    Bridge : AWLM.AccessibleWeilMeetLimitBridge
               {ℓ = ℓ} {ℓW = ℓW} {ℓC = ℓC}
               K RS

  -- End-to-end consequence: GRH_Without_Vacuity_Guards for the induced ζ spectral adapter.
  GRH_Without_Vacuity_Guardsζ : GRH_Without_Vacuity_Guards RS
  GRH_Without_Vacuity_Guardsζ = AWLM.GRH_Without_Vacuity_Guards_from_AccessibleWeilMeetLimitBridge {ℓC = ℓC} K RS Bridge

  -- Definitional alignment helper: in the Dirichlet-series region, the partition-first
  -- ζ value agrees with the Dirichlet-series surrogate (from `RiemannFacts`).
  ζ-partition≡DS
    : ∀ {u} → RiemannFacts.DS F u
    → PZ.PartitionZetaBridge.Z∞ (RiemannFacts.Partition F) u ≡ RiemannFacts.DSVal F u
  ζ-partition≡DS = Partition≡DS F

-- --------------------------------------------------------------------------
-- Standard pack skeleton (uniform API).

module QuartetZetaMeetLimitLedger
  {ℓ ℓW ℓC : Level}
  {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  (F : RiemannFacts)
  where

  Assumptions : Set (lsuc (ℓ ⊔ ℓW ⊔ lsuc ℓC))
  Assumptions = ZetaAccessibleMeetLimitLedger {ℓ = ℓ} {ℓW = ℓW} {ℓC = ℓC} K F

  Claim : Assumptions → Set
  Claim _ = GRH_Without_Vacuity_Guards (RiemannSpectralFromFacts F)

  module Q = Quartet.Make Assumptions Claim
  open Q public using (Pack; assumptionsOf; claimOf)

  mkPack : (A : Assumptions) → Pack
  mkPack = Q.mkPack (ZetaAccessibleMeetLimitLedger.GRH_Without_Vacuity_Guardsζ {F = F})
