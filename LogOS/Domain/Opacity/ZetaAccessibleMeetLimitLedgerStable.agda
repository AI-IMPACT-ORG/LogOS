{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.ZetaAccessibleMeetLimitLedgerStable where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

open import LogOS.Domain.Opacity.NumberTheory.LFunction.RiemannFacts using (RiemannFacts; RiemannSpectralFromFacts; Partition≡DS)
open import LogOS.Domain.Opacity.NumberTheory.LFunction.PartitionZetaBridge as PZ
open import LogOS.Domain.Opacity.NumberTheory.LFunction.ZerosPack using (GRH_Without_Vacuity_Guards)

import LogOS.Domain.Opacity.AccessibleWeilMeetLimitBridgeStable as AWLMS

-- ζ-facing wrapper for the “accessible Weil + meet-limit” route, using the
-- stable-truth refinement:
-- per-regulator observability is derived from stability/extensionality via `Pr`.

record ZetaAccessibleMeetLimitLedgerStable {ℓ ℓW : Level}
                                           {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                                           (K : Kernel Sig Q)
                                           (F : RiemannFacts)
                                           : Set (lsuc (ℓ ⊔ lsuc ℓW)) where
  private
    RS = RiemannSpectralFromFacts F

  field
    Bridge : AWLMS.AccessibleWeilMeetLimitBridgeStable
               {ℓ = ℓ} {ℓW = ℓW}
               K RS

  -- End-to-end consequence: GRH_Without_Vacuity_Guards for the induced ζ spectral adapter.
  GRH_Without_Vacuity_Guardsζ : GRH_Without_Vacuity_Guards RS
  GRH_Without_Vacuity_Guardsζ = AWLMS.AccessibleWeilMeetLimitBridgeStable.GRH_Without_Vacuity_Guards-from-stable-bridge Bridge

  -- Definitional alignment helper: in the Dirichlet-series region, the partition-first
  -- ζ value agrees with the Dirichlet-series surrogate (from `RiemannFacts`).
  ζ-partition≡DS
    : ∀ {u} → RiemannFacts.DS F u
    → PZ.PartitionZetaBridge.Z∞ (RiemannFacts.Partition F) u ≡ RiemannFacts.DSVal F u
  ζ-partition≡DS = Partition≡DS F

-- --------------------------------------------------------------------------
-- Standard pack skeleton (uniform API).

module QuartetZetaMeetLimitLedgerStable
  {ℓ ℓW : Level}
  {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  (F : RiemannFacts)
  where

  Assumptions : Set (lsuc (ℓ ⊔ lsuc ℓW))
  Assumptions = ZetaAccessibleMeetLimitLedgerStable {ℓ = ℓ} {ℓW = ℓW} K F

  Claim : Assumptions → Set
  Claim _ = GRH_Without_Vacuity_Guards (RiemannSpectralFromFacts F)

  record Pack (A : Assumptions) : Set (lsuc (ℓ ⊔ lsuc ℓW)) where
    field
      claim : Claim A

  mkPack : (A : Assumptions) → Pack A
  mkPack A = record { claim = ZetaAccessibleMeetLimitLedgerStable.GRH_Without_Vacuity_Guardsζ A }
