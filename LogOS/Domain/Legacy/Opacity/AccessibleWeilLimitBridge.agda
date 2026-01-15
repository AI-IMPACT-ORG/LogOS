{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Legacy.Opacity.AccessibleWeilLimitBridge where

-- Legacy: superseded by the meet-limit + stable/cofinal bridges.

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

import LogOS.Theorems.Meta.CommunicableTruth as Comm

open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann using (RiemannSpectral)
open import LogOS.Domain.Opacity.NumberTheory.LFunction.ZerosPack using (GRH_Without_Vacuity_Guards)

import LogOS.Domain.Opacity.ZetaTruthLedger as Ledger
import LogOS.Domain.Opacity.AccessibleWeilLedger as AWL
import LogOS.Theorems.Meta.QuartetCore as Quartet

-- Finite → limit bridge pack for the accessible-Weil route:
--
-- You provide:
-- - a target positivity predicate W∞ on the observer language (codes),
-- - a Weil/explicit-formula direction at the limit (probe-pos→OnLine),
-- - a family of finite regulators i ↦ Wᵢ on the same test language,
-- - finite proofs that each regulator can communicate positivity of the probe,
-- - one continuity axiom: if *all* regulators can communicate the probe,
--   then the limit can communicate it too.
--
-- Then GRH_Without_Vacuity_Guards follows by instantiating the `AccessibleWeilLedgerRS` record at RS.

record AccessibleWeilLimitBridge {ℓ ℓW ℓC}
                                 {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                                 (K  : Kernel Sig Q)
                                 (RS : RiemannSpectral)
                                 : Set (lsuc (ℓ ⊔ ℓW ⊔ lsuc ℓC)) where
  open RiemannSpectral RS

  field
    Idx : Set

    -- Limit predicate (“true positivity” for the target L-function).
    W∞ : Kernel.Code K → Set ℓW

    -- Weil direction at the limit: W∞(probe s) ⇒ OnLine s for nontrivial zeros.
    WC∞ : Ledger.ZetaWeilCriterionWeak RS
            (AWL.TruthPositivity-fromPr {ℓC = ℓC} K W∞)

    -- Regulator predicates (finite/truncated approximants).
    Wᵢ : Idx → Kernel.Code K → Set ℓW

    -- Finite completeness: every regulator can communicate positivity of the probe.
    completeᵢ : ∀ i s → NontrivialZero s →
      Comm.Pr {ℓC = ℓC} K (Wᵢ i) (Ledger.ZetaWeilCriterionWeak.probe WC∞ s)

    -- Continuity (the key axiom): communicability of the probe is preserved in the limit.
    complete∞ : ∀ s → NontrivialZero s →
      (∀ i → Comm.Pr {ℓC = ℓC} K (Wᵢ i) (Ledger.ZetaWeilCriterionWeak.probe WC∞ s))
      → Comm.Pr {ℓC = ℓC} K W∞ (Ledger.ZetaWeilCriterionWeak.probe WC∞ s)

-- Build the minimal accessible-Weil ledger at the limit from the bridge data.

mkLedger∞
  : ∀ {ℓ ℓW ℓC}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (RS : RiemannSpectral)
    (B  : AccessibleWeilLimitBridge {ℓ = ℓ} {ℓW = ℓW} {ℓC = ℓC} K RS)
  → AWL.AccessibleWeilLedgerRS {ℓ = ℓ} {ℓW = ℓW} {ℓC = ℓC} K RS
mkLedger∞ {ℓC = ℓC} K RS B =
  record
    { W-pos   = AccessibleWeilLimitBridge.W∞ B
    ; WC      = AccessibleWeilLimitBridge.WC∞ B
    ; complete = λ s nz →
        AccessibleWeilLimitBridge.complete∞ B s nz (λ i → AccessibleWeilLimitBridge.completeᵢ B i s nz)
    }

-- End-to-end: finite regulators + continuity + Weil direction ⇒ GRH_Without_Vacuity_Guards (for RS).

GRH_Without_Vacuity_Guards_from_AccessibleWeilLimitBridge
  : ∀ {ℓ ℓW ℓC}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (RS : RiemannSpectral)
    (B  : AccessibleWeilLimitBridge {ℓ = ℓ} {ℓW = ℓW} {ℓC = ℓC} K RS)
  → GRH_Without_Vacuity_Guards RS
GRH_Without_Vacuity_Guards_from_AccessibleWeilLimitBridge {ℓC = ℓC} K RS B =
  AWL.GRH_Without_Vacuity_Guards_from_AccessibleWeilLedgerRS {ℓC = ℓC} K RS (mkLedger∞ {ℓC = ℓC} K RS B)

-- --------------------------------------------------------------------------
-- Standard pack skeleton (uniform API).

module QuartetLimitBridge
  {ℓ ℓW ℓC}
  {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K  : Kernel Sig Q)
  (RS : RiemannSpectral)
  where

  Assumptions : Set (lsuc (ℓ ⊔ ℓW ⊔ lsuc ℓC))
  Assumptions = AccessibleWeilLimitBridge {ℓ = ℓ} {ℓW = ℓW} {ℓC = ℓC} K RS

  Claim : Assumptions → Set
  Claim _ = GRH_Without_Vacuity_Guards RS

  module Q = Quartet.Make Assumptions Claim
  open Q public using (Pack; assumptionsOf; claimOf)

  mkPack : (A : Assumptions) → Pack
  mkPack = Q.mkPack (GRH_Without_Vacuity_Guards_from_AccessibleWeilLimitBridge {ℓC = ℓC} K RS)
