{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.AccessibleWeilLedger where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

import LogOS.Theorems.Meta.CommunicableTruth as Comm
open import LogOS.Theorems.Meta.MathTruth public using (TruthPositivity-fromPr)

open import LogOS.Domain.Opacity.NumberTheory.LFunction.RiemannFacts using (RiemannFacts; RiemannSpectralFromFacts)
open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann using (RiemannSpectral)
open import LogOS.Domain.Opacity.NumberTheory.LFunction.ZerosPack using (GRH_Without_Vacuity_Guards)

import LogOS.Domain.Opacity.ZetaTruthLedger as Ledger

-- General (L-function–agnostic) ledger: parameterize by a spectral adapter RS.
-- This is the clean statement for “GRH_Without_Vacuity_Guards for an L-function”, once RS packages:
--   - the nontrivial zeros (in a strip),
--   - the target critical-line predicate OnLine.

record AccessibleWeilLedgerRS {ℓ ℓW ℓC}
                              {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                              (K  : Kernel Sig Q)
                              (RS : RiemannSpectral)
                              : Set (lsuc (ℓ ⊔ ℓW ⊔ lsuc ℓC)) where
  open RiemannSpectral RS
  field
    W-pos : Kernel.Code K → Set ℓW

    -- Weil direction (no “observability” assumed here).
    WC : Ledger.ZetaWeilCriterionWeak RS
           (TruthPositivity-fromPr {ℓC = ℓC} K W-pos)

    -- Observational completeness for probes (the only “observer” axiom):
    complete : ∀ s → NontrivialZero s →
      Comm.Pr {ℓC = ℓC} K W-pos (Ledger.ZetaWeilCriterionWeak.probe WC s)

GRH_Without_Vacuity_Guards_from_AccessibleWeilLedgerRS
  : ∀ {ℓ ℓW ℓC}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (RS : RiemannSpectral)
    (L  : AccessibleWeilLedgerRS {ℓ = ℓ} {ℓW = ℓW} {ℓC = ℓC} K RS)
  → GRH_Without_Vacuity_Guards RS
GRH_Without_Vacuity_Guards_from_AccessibleWeilLedgerRS {ℓC = ℓC} K RS L =
  Ledger.GRH_Without_Vacuity_Guards-from-weak-ledger+complete
    RS
    (TruthPositivity-fromPr {ℓC = ℓC} K (AccessibleWeilLedgerRS.W-pos L))
    (AccessibleWeilLedgerRS.WC L)
    (AccessibleWeilLedgerRS.complete L)

-- Minimal axiom ledger for GRH_Without_Vacuity_Guards with an “accessible truth” semantics:
-- - choose a kernel K (observer language + Flow),
-- - choose a predicate W-pos on codes (the “positivity/validity” notion on tests),
-- - assume the (textbook) Weil/explicit-formula direction: W-pos(probe s) ⇒ OnLine s,
-- - assume observational completeness only for the probe family: each nontrivial zero
--   yields a probe that is communicable/observable, i.e. in Pr(W-pos).
--
-- Everything else (in particular positivity-on-observables) is derived.

record AccessibleWeilLedger {ℓ ℓW ℓC}
                            {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                            (K : Kernel Sig Q)
                            (F : RiemannFacts)
                            : Set (lsuc (ℓ ⊔ ℓW ⊔ lsuc ℓC)) where
  private
    RS : RiemannSpectral
    RS = RiemannSpectralFromFacts F

  open RiemannSpectral RS

  field
    W-pos : Kernel.Code K → Set ℓW

    -- Weil direction (no “observability” assumed here).
    WC : Ledger.ZetaWeilCriterionWeak RS
           (TruthPositivity-fromPr {ℓC = ℓC} K W-pos)

    -- Observational completeness for probes (the only “observer” axiom):
    complete : ∀ s → NontrivialZero s →
      Comm.Pr {ℓC = ℓC} K W-pos (Ledger.ZetaWeilCriterionWeak.probe WC s)

-- One-line consequence: the above ledger yields standard GRH_Without_Vacuity_Guards for the induced
-- Riemann spectral pack.

GRH_Without_Vacuity_Guards_from_AccessibleWeilLedger
  : ∀ {ℓ ℓW ℓC}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (F : RiemannFacts)
    (L : AccessibleWeilLedger {ℓ = ℓ} {ℓW = ℓW} {ℓC = ℓC} K F)
  → GRH_Without_Vacuity_Guards (RiemannSpectralFromFacts F)
GRH_Without_Vacuity_Guards_from_AccessibleWeilLedger {ℓC = ℓC} K F L =
  Ledger.GRH_Without_Vacuity_Guards-from-weak-ledger+complete
    (RiemannSpectralFromFacts F)
    (TruthPositivity-fromPr {ℓC = ℓC} K (AccessibleWeilLedger.W-pos L))
    (AccessibleWeilLedger.WC L)
    (AccessibleWeilLedger.complete L)

-- --------------------------------------------------------------------------
-- Standard pack skeletons (uniform API).

module QuartetRS
  {ℓ ℓW ℓC}
  {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K  : Kernel Sig Q)
  (RS : RiemannSpectral)
  where

  Assumptions : Set (lsuc (ℓ ⊔ ℓW ⊔ lsuc ℓC))
  Assumptions = AccessibleWeilLedgerRS {ℓ = ℓ} {ℓW = ℓW} {ℓC = ℓC} K RS

  Claim : Assumptions → Set
  Claim _ = GRH_Without_Vacuity_Guards RS

  record Pack (A : Assumptions) : Set (lsuc (ℓ ⊔ ℓW ⊔ lsuc ℓC)) where
    field
      claim : Claim A

  mkPack : (A : Assumptions) → Pack A
  mkPack A = record { claim = GRH_Without_Vacuity_Guards_from_AccessibleWeilLedgerRS {ℓC = ℓC} K RS A }

module QuartetZeta
  {ℓ ℓW ℓC}
  {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  (F : RiemannFacts)
  where

  Assumptions : Set (lsuc (ℓ ⊔ ℓW ⊔ lsuc ℓC))
  Assumptions = AccessibleWeilLedger {ℓ = ℓ} {ℓW = ℓW} {ℓC = ℓC} K F

  Claim : Assumptions → Set
  Claim _ = GRH_Without_Vacuity_Guards (RiemannSpectralFromFacts F)

  record Pack (A : Assumptions) : Set (lsuc (ℓ ⊔ ℓW ⊔ lsuc ℓC)) where
    field
      claim : Claim A

  mkPack : (A : Assumptions) → Pack A
  mkPack A = record { claim = GRH_Without_Vacuity_Guards_from_AccessibleWeilLedger {ℓC = ℓC} K F A }
