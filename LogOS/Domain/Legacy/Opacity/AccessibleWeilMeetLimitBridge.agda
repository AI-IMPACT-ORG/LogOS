{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Legacy.Opacity.AccessibleWeilMeetLimitBridge where

-- Legacy: direct meet-limit bridge without stable/cofinal refinements.

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

import LogOS.Theorems.Meta.CommunicableTruth as Comm
import LogOS.Theorems.Meta.MathTruth as MT

open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann using (RiemannSpectral)
open import LogOS.Domain.Opacity.NumberTheory.LFunction.ZerosPack using (GRH_Without_Vacuity_Guards)

import LogOS.Domain.Opacity.ZetaTruthLedger as Ledger
import LogOS.Domain.Legacy.Opacity.AccessibleWeilLimitBridge as AWLB
import LogOS.Theorems.Meta.QuartetCore as Quartet

-- A minimal “Weil probe” interface that does not mention observability at all:
-- it is just the probe constructor plus the implication W(probe s) ⇒ OnLine s.
--
-- This is the only ζ/analytic ingredient needed by the accessible-truth route.

record WeilProbeImplication {ℓS ℓW : Level}
                            (RS : RiemannSpectral)
                            (W  : Set ℓS)
                            (W-pos : W → Set ℓW)
                            : Set (lsuc (ℓS ⊔ ℓW)) where
  open RiemannSpectral RS
  field
    probe : Spectral → W
    probe-pos→OnLine : ∀ s → NontrivialZero s → W-pos (probe s) → OnLine s

-- A more “LogOS-native” limit story:
-- define the limit predicate W∞ as the pointwise intersection (Π/∧) of all
-- finite regulators Wᵢ. Then the limit preservation clause becomes a lemma
-- (via `MathTruth.allObservableᵢ→Observable∞` / `Comm.Pr-Π`), not an extra axiom.

record AccessibleWeilMeetLimitBridge {ℓ ℓW ℓC}
                                     {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                                     (K  : Kernel Sig Q)
                                     (RS : RiemannSpectral)
                                     : Set (lsuc (ℓ ⊔ ℓW ⊔ lsuc ℓC)) where
  open RiemannSpectral RS

  field
    -- Finite regulators packaged as a generic “MathTruth” meet-limit:
    -- Wᵢ are the finite predicates, W∞ is their intersection, and `Pr` provides
    -- the canonical communicable fragment.
    Reg : MT.MathTruth {ℓ} {ℓW} {ℓC} K

  open MT.MathTruth Reg public
    renaming (Idx to Idx; Truthᵢ to Wᵢ; Truth∞ to W∞)

  field
    -- Weil direction at the limit (still analytic content, fully explicit):
    -- W∞(probe s) ⇒ OnLine s for nontrivial zeros.
    WProbe : WeilProbeImplication RS (Kernel.Code K) W∞

    -- Finite completeness: every regulator can communicate positivity of the probe.
    completeᵢ : ∀ i s → NontrivialZero s →
      Comm.Pr {ℓC = ℓC} K (Wᵢ i) (WeilProbeImplication.probe WProbe s)

  -- Derived continuity: communicability of the probe is preserved at the limit
  -- because `Pr` preserves intersections of truth predicates (built into MathTruth).
  complete∞ : ∀ s → NontrivialZero s →
    (∀ i → Comm.Pr {ℓC = ℓC} K (Wᵢ i) (WeilProbeImplication.probe WProbe s))
    → Comm.Pr {ℓC = ℓC} K W∞ (WeilProbeImplication.probe WProbe s)
  complete∞ s nz all = allObservableᵢ→Observable∞ all

  -- Package the probe interface back into the generic ledger’s weak Weil record
  -- so we can reuse the existing GRH_Without_Vacuity_Guards bridge theorem.

  WC∞ : Ledger.ZetaWeilCriterionWeak RS
          (MT.TruthPositivity-fromPr {ℓC = ℓC} K W∞)
  WC∞ = record
    { probe = WeilProbeImplication.probe WProbe
    ; probe-pos→OnLine = WeilProbeImplication.probe-pos→OnLine WProbe
    }

-- Build the general finite→limit bridge from the meet-limit bridge.

toLimitBridge
  : ∀ {ℓ ℓW ℓC}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (RS : RiemannSpectral)
    (B  : AccessibleWeilMeetLimitBridge {ℓ = ℓ} {ℓW = ℓW} {ℓC = ℓC} K RS)
  → AWLB.AccessibleWeilLimitBridge {ℓ = ℓ} {ℓW = ℓW} {ℓC = ℓC} K RS
toLimitBridge {ℓC = ℓC} K RS B =
  record
    { Idx       = AccessibleWeilMeetLimitBridge.Idx B
    ; W∞        = AccessibleWeilMeetLimitBridge.W∞ B
    ; WC∞       = AccessibleWeilMeetLimitBridge.WC∞ B
    ; Wᵢ        = AccessibleWeilMeetLimitBridge.Wᵢ B
    ; completeᵢ = AccessibleWeilMeetLimitBridge.completeᵢ B
    ; complete∞ = AccessibleWeilMeetLimitBridge.complete∞ {ℓC = ℓC} B
    }

GRH_Without_Vacuity_Guards_from_AccessibleWeilMeetLimitBridge
  : ∀ {ℓ ℓW ℓC}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (RS : RiemannSpectral)
    (B  : AccessibleWeilMeetLimitBridge {ℓ = ℓ} {ℓW = ℓW} {ℓC = ℓC} K RS)
  → GRH_Without_Vacuity_Guards RS
GRH_Without_Vacuity_Guards_from_AccessibleWeilMeetLimitBridge {ℓC = ℓC} K RS B =
  AWLB.GRH_Without_Vacuity_Guards_from_AccessibleWeilLimitBridge {ℓC = ℓC} K RS (toLimitBridge {ℓC = ℓC} K RS B)

-- --------------------------------------------------------------------------
-- Standard pack skeleton (uniform API).

module QuartetMeetLimitBridge
  {ℓ ℓW ℓC}
  {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K  : Kernel Sig Q)
  (RS : RiemannSpectral)
  where

  Assumptions : Set (lsuc (ℓ ⊔ ℓW ⊔ lsuc ℓC))
  Assumptions = AccessibleWeilMeetLimitBridge {ℓ = ℓ} {ℓW = ℓW} {ℓC = ℓC} K RS

  Claim : Assumptions → Set
  Claim _ = GRH_Without_Vacuity_Guards RS

  module Q = Quartet.Make Assumptions Claim
  open Q public using (Pack; assumptionsOf; claimOf)

  mkPack : (A : Assumptions) → Pack
  mkPack = Q.mkPack (GRH_Without_Vacuity_Guards_from_AccessibleWeilMeetLimitBridge {ℓC = ℓC} K RS)
