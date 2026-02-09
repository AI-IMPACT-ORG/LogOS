{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.AccessibleWeilLedger where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

import LogOS.Theorems.Meta.CommunicableTruth as Comm
open import LogOS.Theorems.Meta.MathTruth public using (TruthPositivity-fromPr)
import LogOS.Theorems.Meta.LimitPublicisation as LP

open import LogOS.Domain.Opacity.NumberTheory.LFunction.RiemannFacts using (RiemannFacts; RiemannSpectralFromFacts)
open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann using (RiemannSpectral)
open import LogOS.Domain.Opacity.NumberTheory.LFunction.ZerosPack using (GRH_Without_Vacuity_Guards)
open import LogOS.Ports.Semantic.SatMor using (SatRefinement₀; sat-→₀)

import LogOS.Domain.Opacity.WeilProbeImplication as WPI
import LogOS.Domain.Opacity.WeilCriterionLedger as WCL
import LogOS.Theorems.Meta.ApplicationKit as AppKit

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
    WC : WCL.WeilCriterionWeak RS
           (TruthPositivity-fromPr {ℓC = ℓC} K W-pos)

    -- Observational completeness for probes (the only “observer” axiom):
    complete-ref : SatRefinement₀ (RiemannSpectral.Spectral RS)
                    (λ _ s → NontrivialZero s)
                    (λ _ s → Comm.Pr {ℓC = ℓC} K W-pos
                              (WCL.WeilCriterionWeak.probe WC s))

  complete : ∀ s → NontrivialZero s →
    Comm.Pr {ℓC = ℓC} K W-pos (WCL.WeilCriterionWeak.probe WC s)
  complete s nz = sat-→₀ complete-ref s nz

GRH_Without_Vacuity_Guards_from_AccessibleWeilLedgerRS
  : ∀ {ℓ ℓW ℓC}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (RS : RiemannSpectral)
    (L  : AccessibleWeilLedgerRS {ℓ = ℓ} {ℓW = ℓW} {ℓC = ℓC} K RS)
  → GRH_Without_Vacuity_Guards RS
GRH_Without_Vacuity_Guards_from_AccessibleWeilLedgerRS {ℓC = ℓC} K RS L =
  WCL.GRH_Without_Vacuity_Guards-from-weak-criterion+complete
    RS
    (TruthPositivity-fromPr {ℓC = ℓC} K (AccessibleWeilLedgerRS.W-pos L))
    (AccessibleWeilLedgerRS.WC L)
    (AccessibleWeilLedgerRS.complete-ref L)

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
    WC : WCL.WeilCriterionWeak RS
           (TruthPositivity-fromPr {ℓC = ℓC} K W-pos)

    -- Observational completeness for probes (the only “observer” axiom):
    complete-ref : SatRefinement₀ (RiemannSpectral.Spectral RS)
                    (λ _ s → NontrivialZero s)
                    (λ _ s → Comm.Pr {ℓC = ℓC} K W-pos
                              (WCL.WeilCriterionWeak.probe WC s))

  complete : ∀ s → NontrivialZero s →
    Comm.Pr {ℓC = ℓC} K W-pos (WCL.WeilCriterionWeak.probe WC s)
  complete s nz = sat-→₀ complete-ref s nz

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
  WCL.GRH_Without_Vacuity_Guards-from-weak-criterion+complete
    (RiemannSpectralFromFacts F)
    (TruthPositivity-fromPr {ℓC = ℓC} K (AccessibleWeilLedger.W-pos L))
    (AccessibleWeilLedger.WC L)
    (AccessibleWeilLedger.complete-ref L)

-- --------------------------------------------------------------------------
-- Strengthening: kernel-stable truth implies probe observability.
--
-- If `W-pos` is itself decode-extensional and stable under the kernel’s closure
-- modality at the chosen computational step (`BoxAt step ∘ Body`), then a *plain*
-- truth fact `W-pos (probe s)` upgrades to the probe observability premise
-- `Pr W-pos (probe s)`.
--
-- Mechanically this is discharged by `LP.TruthK→Pr-BoxBody` (which internally
-- transports Box∘Body-stability to FlowCode-stability using decode-extensionality).

record AccessibleWeilLedgerRSStableTruth {ℓ ℓW : Level}
                                         {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                                         (K  : Kernel Sig Q)
                                         (RS : RiemannSpectral)
                                         : Set (lsuc ℓ ⊔ lsuc ℓW) where
  open RiemannSpectral RS
  field
    W-pos : Kernel.Code K → Set ℓW
    WProbe : WPI.WeilProbeImplication RS (Kernel.Code K) W-pos

    W-ext    : Comm.DecodeExtensional′ K W-pos
    W-stableBoxBody
      : ∀ γ → W-pos γ ↔ W-pos (BoxAt K (GTier.step (Kernel.G K)) (Kernel.Body K γ))

    holds-probe
      : ∀ s → NontrivialZero s
        → W-pos (WPI.WeilProbeImplication.probe WProbe s)

  WC : WCL.WeilCriterionWeak RS
          (TruthPositivity-fromPr {ℓC = ℓW} K W-pos)
  WC = record
    { probe = WPI.WeilProbeImplication.probe WProbe
    ; probe-pos-ref =
        record
          { sat-→ = λ _ s p →
              WPI.WeilProbeImplication.probe-pos→OnLine WProbe s (fst p) (snd p)
          }
    }

  complete-ref
    : SatRefinement₀ (RiemannSpectral.Spectral RS)
        (λ _ s → NontrivialZero s)
        (λ _ s → Comm.Pr {ℓC = ℓW} K W-pos
                  (WCL.WeilCriterionWeak.probe WC s))
  complete-ref = record
    { sat-→ = λ _ s nz →
        LP.TruthK→Pr-BoxBody K W-pos W-ext W-stableBoxBody (holds-probe s nz)
    }

  toAccessibleWeilLedgerRS
    : AccessibleWeilLedgerRS {ℓ = ℓ} {ℓW = ℓW} {ℓC = ℓW} K RS
  toAccessibleWeilLedgerRS = record
    { W-pos        = W-pos
    ; WC           = WC
    ; complete-ref = complete-ref
    }

  GRH_Without_Vacuity_Guards-from-stableTruth-ledger : GRH_Without_Vacuity_Guards RS
  GRH_Without_Vacuity_Guards-from-stableTruth-ledger =
    GRH_Without_Vacuity_Guards_from_AccessibleWeilLedgerRS {ℓC = ℓW} K RS toAccessibleWeilLedgerRS

record AccessibleWeilLedgerStableTruth {ℓ ℓW : Level}
                                       {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                                       (K : Kernel Sig Q)
                                       (F : RiemannFacts)
                                       : Set (lsuc ℓ ⊔ lsuc ℓW) where
  private
    RS : RiemannSpectral
    RS = RiemannSpectralFromFacts F

  open RiemannSpectral RS

  field
    W-pos : Kernel.Code K → Set ℓW
    WProbe : WPI.WeilProbeImplication RS (Kernel.Code K) W-pos

    W-ext    : Comm.DecodeExtensional′ K W-pos
    W-stableBoxBody
      : ∀ γ → W-pos γ ↔ W-pos (BoxAt K (GTier.step (Kernel.G K)) (Kernel.Body K γ))

    holds-probe
      : ∀ s → NontrivialZero s
        → W-pos (WPI.WeilProbeImplication.probe WProbe s)

  RSStableTruth : AccessibleWeilLedgerRSStableTruth {ℓ = ℓ} {ℓW = ℓW} K RS
  RSStableTruth = record
    { W-pos       = W-pos
    ; WProbe      = WProbe
    ; W-ext       = W-ext
    ; W-stableBoxBody = W-stableBoxBody
    ; holds-probe = holds-probe
    }

  GRH_Without_Vacuity_Guardsζ : GRH_Without_Vacuity_Guards RS
  GRH_Without_Vacuity_Guardsζ =
    AccessibleWeilLedgerRSStableTruth.GRH_Without_Vacuity_Guards-from-stableTruth-ledger RSStableTruth

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

  module Q =
    AppKit.MakeDerived Assumptions Claim
      (GRH_Without_Vacuity_Guards_from_AccessibleWeilLedgerRS {ℓC = ℓC} K RS)
  open Q public using (Pack; assumptionsOf; claimOf; mkPack)

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

  module Q =
    AppKit.MakeDerived Assumptions Claim
      (GRH_Without_Vacuity_Guards_from_AccessibleWeilLedger {ℓC = ℓC} K F)
  open Q public using (Pack; assumptionsOf; claimOf; mkPack)

module QuartetRSStableTruth
  {ℓ ℓW}
  {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K  : Kernel Sig Q)
  (RS : RiemannSpectral)
  where

  Assumptions : Set (lsuc ℓ ⊔ lsuc ℓW)
  Assumptions = AccessibleWeilLedgerRSStableTruth {ℓ = ℓ} {ℓW = ℓW} K RS

  Claim : Assumptions → Set
  Claim _ = GRH_Without_Vacuity_Guards RS

  module Q =
    AppKit.MakeDerived Assumptions Claim
      (AccessibleWeilLedgerRSStableTruth.GRH_Without_Vacuity_Guards-from-stableTruth-ledger {RS = RS})
  open Q public using (Pack; assumptionsOf; claimOf; mkPack)

module QuartetZetaStableTruth
  {ℓ ℓW}
  {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  (F : RiemannFacts)
  where

  Assumptions : Set (lsuc ℓ ⊔ lsuc ℓW)
  Assumptions = AccessibleWeilLedgerStableTruth {ℓ = ℓ} {ℓW = ℓW} K F

  Claim : Assumptions → Set
  Claim _ = GRH_Without_Vacuity_Guards (RiemannSpectralFromFacts F)

  module Q =
    AppKit.MakeDerived Assumptions Claim
      (AccessibleWeilLedgerStableTruth.GRH_Without_Vacuity_Guardsζ {F = F})
  open Q public using (Pack; assumptionsOf; claimOf; mkPack)
