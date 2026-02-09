{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.ZetaTruthLedger where

open import LogOS.Prelude

open import LogOS.Domain.Opacity.NumberTheory.LFunction.RiemannFacts using (RiemannFacts; RiemannSpectralFromFacts)
open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann using (RiemannSpectral)
open import LogOS.Domain.Opacity.NumberTheory.LFunction.ZerosPack using (GRH_Without_Vacuity_Guards)
import LogOS.Domain.Opacity.Meaningfulness as Meaning

import LogOS.Theorems.Meta.TruthPositivity as TP
open TP public using (TruthPositivity)

import LogOS.Domain.Opacity.WeilCriterionLedger as WCL
open WCL public renaming
  ( WeilCriterion to ZetaWeilCriterion
  ; WeilCriterionWeak to ZetaWeilCriterionWeak
  ; GRH_Without_Vacuity_Guards-from-weak-criterion+complete to GRH_Without_Vacuity_Guards-from-weak-ledger+complete
  )

import LogOS.Theorems.Meta.ApplicationKit as AppKit

-- This module is an “axiom ledger” packaging: it isolates exactly what you must
-- assume (beyond LogOS core) to derive the standard RH/GRH_Without_Vacuity_Guards statement.
--
-- Philosophy:
-- - “ζ facts” are a textbook-aligned record (`RiemannFacts`) that can be refined
--   toward a literal Dirichlet-series definition (`DS`, `DSVal`, `zeta≡DS`) and/or
--   a regulator-first “partition function” presentation (`RiemannFacts.Partition`).
-- - “truth facts” are a general positivity principle on *observable* tests.
-- - “bridge facts” are the well-known Weil/explicit-formula clause: for each
--   nontrivial zero, there is a probe test whose positivity forces `OnLine`.

-- One-line theorem: from (1) ζ facts, (2) truth-positivity, (3) Weil criterion,
-- conclude RH/GRH_Without_Vacuity_Guards (i.e. every nontrivial zero lies on the line).

RH_from_Ledger
  : ∀ {ℓT ℓW ℓObs}
    (F  : RiemannFacts)
    (TPo : TP.TruthPositivity {ℓT} {ℓW} {ℓObs})
    (WC : ZetaWeilCriterion (RiemannSpectralFromFacts F) TPo)
  → GRH_Without_Vacuity_Guards (RiemannSpectralFromFacts F)
RH_from_Ledger F TPo WC =
  WCL.GRH_Without_Vacuity_Guards-from-WeilCriterion (RiemannSpectralFromFacts F) TPo WC

-- Convenience: derive the same ledger theorem when TruthPositivity is defined
-- via a partial witness surface (certificate-based observability).

RH_from_Ledger_viaPartialWitness
  : ∀ {ℓT ℓW}
    (F : RiemannFacts)
    {Test : Set ℓT}
    {W-pos : Test → Set ℓW}
    (PW : TP.PartialWitness Test W-pos)
    (WC : ZetaWeilCriterion (RiemannSpectralFromFacts F)
            (TP.fromPartialWitness PW))
  → GRH_Without_Vacuity_Guards (RiemannSpectralFromFacts F)
RH_from_Ledger_viaPartialWitness F PW WC =
  RH_from_Ledger F (TP.fromPartialWitness PW) WC

-- Convenience: the same ledger theorem when observability is “there exists a
-- checkable proof object”, i.e. Metamath-style certificates.

RH_from_Ledger_viaProofWitness
  : ∀ {ℓT ℓW ℓP}
    (F : RiemannFacts)
    {Test : Set ℓT}
    {W-pos : Test → Set ℓW}
    (PW : TP.ProofWitness {ℓP = ℓP} Test W-pos)
    (WC : ZetaWeilCriterion (RiemannSpectralFromFacts F)
            (TP.fromProofWitness PW))
  → GRH_Without_Vacuity_Guards (RiemannSpectralFromFacts F)
RH_from_Ledger_viaProofWitness F PW WC =
  RH_from_Ledger F (TP.fromProofWitness PW) WC

-- Convenience packaging: expose the RH/GRH_Without_Vacuity_Guards route as an explicit axiom ledger record.

record RHAxiomLedger {ℓT ℓW ℓObs : Level} : Set (lsuc (ℓT ⊔ ℓW ⊔ ℓObs)) where
  field
    F   : RiemannFacts
    VacuityGuards : Meaning.VacuityGuards (RiemannSpectralFromFacts F)
    TPo : TP.TruthPositivity {ℓT} {ℓW} {ℓObs}
    WC  : ZetaWeilCriterion (RiemannSpectralFromFacts F) TPo

RH_from_AxiomLedger
  : ∀ {ℓT ℓW ℓObs}
    (L : RHAxiomLedger {ℓT} {ℓW} {ℓObs})
  → GRH_Without_Vacuity_Guards (RiemannSpectralFromFacts (RHAxiomLedger.F L))
RH_from_AxiomLedger L =
  RH_from_Ledger (RHAxiomLedger.F L) (RHAxiomLedger.TPo L) (RHAxiomLedger.WC L)

-- Literature-aligned aliases (André Weil): prefer these names going forward.
WeilCriterion      = WCL.WeilCriterion
WeilCriterionWeak  = WCL.WeilCriterionWeak

-- --------------------------------------------------------------------------
-- Standard pack skeleton (uniform API).
--
-- This is the “axiom ledger” entry: the assumptions are exactly `RHAxiomLedger`,
-- and the resulting claim is the GRH/RH predicate for the induced ζ spectral pack.

module QuartetAxiomLedger {ℓT ℓW ℓObs : Level} where
  Assumptions : Set (lsuc (ℓT ⊔ ℓW ⊔ ℓObs))
  Assumptions = RHAxiomLedger {ℓT} {ℓW} {ℓObs}

  Claim : Assumptions → Set
  Claim A = GRH_Without_Vacuity_Guards (RiemannSpectralFromFacts (RHAxiomLedger.F A))

  module Q = AppKit.MakeDerived Assumptions Claim RH_from_AxiomLedger
  open Q public using (Pack; assumptionsOf; claimOf; mkPack)
