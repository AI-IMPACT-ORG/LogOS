{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.GRH_Vacuity_Guards where

open import LogOS.Prelude
open import LogOS.Prelude.Product using (Σ; _,_)

open import LogOS.Domain.Opacity.NumberTheory.LFunction.RiemannFacts using (RiemannFacts; RiemannSpectralFromFacts)
open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann using (RiemannSpectral)
open import LogOS.Domain.Opacity.NumberTheory.LFunction.ZerosPack using (GRH_Without_Vacuity_Guards)

import LogOS.Domain.Opacity.Meaningfulness as Meaning
import LogOS.Domain.Opacity.ZetaTruthLedger as Ledger
import LogOS.Theorems.Meta.ApplicationKit as AppKit

-- GRH with vacuity guards:
-- bundle a GRH proof together with explicit non-vacuity / non-tautology guards
-- on the chosen spectral adapter.

record GRH (RS : RiemannSpectral) : Set₁ where
  field
    vacuityGuards : Meaning.VacuityGuards RS
    grh           : GRH_Without_Vacuity_Guards RS

mkGRH
  : ∀ {RS : RiemannSpectral}
  → Meaning.VacuityGuards RS
  → GRH_Without_Vacuity_Guards RS
  → GRH RS
mkGRH vacuityGuards grh = record { vacuityGuards = vacuityGuards ; grh = grh }

-- ζ/ξ-facing (Riemann) packaging: the ledger already isolates all analytic content,
-- and the vacuity guards are explicit.

record RHLedger {ℓT ℓW ℓObs : Level} : Set (lsuc (ℓT ⊔ ℓW ⊔ ℓObs)) where
  field
    F       : RiemannFacts
    vacuityGuards : Meaning.VacuityGuards (RiemannSpectralFromFacts F)
    TPo     : Ledger.TruthPositivity {ℓT} {ℓW} {ℓObs}
    WC      : Ledger.ZetaWeilCriterion (RiemannSpectralFromFacts F) TPo

RH_from_RHLedger
  : ∀ {ℓT ℓW ℓObs}
    (L : RHLedger {ℓT} {ℓW} {ℓObs})
  → GRH (RiemannSpectralFromFacts (RHLedger.F L))
RH_from_RHLedger L =
  mkGRH
    (RHLedger.vacuityGuards L)
    (Ledger.RH_from_Ledger (RHLedger.F L)
      (RHLedger.TPo L)
      (RHLedger.WC L))

-- Convenience: upgrade the existing `RHAxiomLedger` (which already carries the
-- vacuity guards) to the GRH-with-guards packaged claim.

RH_from_AxiomLedger
  : ∀ {ℓT ℓW ℓObs}
    (L : Ledger.RHAxiomLedger {ℓT} {ℓW} {ℓObs})
  → GRH (RiemannSpectralFromFacts (Ledger.RHAxiomLedger.F L))
RH_from_AxiomLedger L =
  mkGRH
    (Ledger.RHAxiomLedger.VacuityGuards L)
    (Ledger.RH_from_AxiomLedger L)

-- --------------------------------------------------------------------------
-- Standard pack skeleton (uniform API).
--
-- This is the “one metalogical assumption + known analytic implication” route:
-- package the assumptions in a ledger and expose the resulting GRH claim as a
-- single predictable `mkPack`.

Assumptions = RHLedger

Claim
  : ∀ {ℓT ℓW ℓObs}
    (A : Assumptions {ℓT} {ℓW} {ℓObs})
  → Set₁
Claim A = GRH (RiemannSpectralFromFacts (RHLedger.F A))

module Q {ℓT ℓW ℓObs : Level} =
  AppKit.MakeDerived
    (Assumptions {ℓT} {ℓW} {ℓObs})
    (Claim {ℓT} {ℓW} {ℓObs})
    RH_from_RHLedger
open Q public using (Pack; assumptionsOf; claimOf; mkPack)
