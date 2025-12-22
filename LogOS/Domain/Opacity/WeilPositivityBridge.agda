{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.WeilPositivityBridge where

open import LogOS.Prelude

open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann
open import LogOS.Domain.Opacity.NumberTheory.LFunction.ZerosPack using (GRH_Without_Vacuity_Guards)

-- Weil criterion route (schematic, explicit-formula positivity):
-- A “Weil functional” W on a space of test objects is assumed positive
-- on all tests. A separate, ζ-specific analytic lemma says that any
-- off-line nontrivial zero yields a probe test on which positivity would fail.
-- We package the analytic content in a *direct* implication:
--     W-pos (probe s)  ⇒  OnLine s
-- for any nontrivial zero s. This keeps the result constructive and matches the
-- existing “fixedness ⇒ OnLine” style of other GRH_Without_Vacuity_Guards bridges.
--
-- This is intended to model the classical “Weil's criterion / explicit formula
-- positivity” equivalence to RH/GRH_Without_Vacuity_Guards (André Weil), without committing to a
-- particular test space.

record WeilPositivityAssumptions {ℓT ℓW : Level}
                                 (RS : RiemannSpectral)
                                 : Set (lsuc (ℓT ⊔ ℓW)) where
  open RiemannSpectral RS
  field
    -- Space of admissible tests (e.g. Schwartz/Bruhat functions, kernels, …)
    Test : Set ℓT

    -- “W is positive on t” (abstract predicate; concrete models can interpret this
    -- as ≥ 0 for a quadratic form W(t⋆t*), or positive semidefiniteness, etc.)
    W-pos : Test → Set ℓW

    -- Global positivity axiom: W-pos holds for every admissible test.
    positivity : ∀ t → W-pos t

    -- A probe extracted from a spectral point (intuitively: a test isolating that zero).
    probe : Spectral → Test

    -- ζ-specific analytic lemma (schematic): for a nontrivial zero, positivity of the
    -- associated probe forces the critical-line property.
    probe-pos→OnLine
      : ∀ s → NontrivialZero s → W-pos (probe s) → OnLine s

-- Consequence: GRH_Without_Vacuity_Guards (for the chosen OnLine predicate) from Weil's criterion.

GRH_Without_Vacuity_Guards_from_WeilPositivity
  : ∀ {ℓT ℓW}
    (RS : RiemannSpectral)
    (A  : WeilPositivityAssumptions {ℓT} {ℓW} RS)
  → ∀ s → RiemannSpectral.NontrivialZero RS s → RiemannSpectral.OnLine RS s
GRH_Without_Vacuity_Guards_from_WeilPositivity RS A s nz =
  let open WeilPositivityAssumptions A in
  probe-pos→OnLine s nz (positivity (probe s))

-- Observer-facing variant: positivity is only assumed for a designated class of
-- tests (e.g. computable/constructible/finite-budget probes), and each relevant
-- zero must yield an observable probe.

record WeilPositivityObservable {ℓT ℓW ℓObs : Level}
                                (RS : RiemannSpectral)
                                : Set (lsuc (ℓT ⊔ ℓW ⊔ ℓObs)) where
  open RiemannSpectral RS
  field
    Test : Set ℓT
    W-pos : Test → Set ℓW

    Observable : Test → Set ℓObs
    positivity : ∀ t → Observable t → W-pos t

    probe : Spectral → Test
    probe-observable : ∀ s → NontrivialZero s → Observable (probe s)

    probe-pos→OnLine : ∀ s → NontrivialZero s → W-pos (probe s) → OnLine s

GRH_Without_Vacuity_Guards_from_WeilPositivityObservable
  : ∀ {ℓT ℓW ℓObs}
    (RS : RiemannSpectral)
    (A  : WeilPositivityObservable {ℓT} {ℓW} {ℓObs} RS)
  → ∀ s → RiemannSpectral.NontrivialZero RS s → RiemannSpectral.OnLine RS s
GRH_Without_Vacuity_Guards_from_WeilPositivityObservable RS A s nz =
  let open WeilPositivityObservable A in
  probe-pos→OnLine s nz (positivity (probe s) (probe-observable s nz))

-- Literature-aligned naming aliases: “Weil criterion” rather than “Weil positivity”.

WeilCriterionAssumptions = WeilPositivityAssumptions
WeilCriterionObservable  = WeilPositivityObservable

GRH_Without_Vacuity_Guards_from_WeilCriterion = GRH_Without_Vacuity_Guards_from_WeilPositivity
GRH_Without_Vacuity_Guards_from_WeilCriterionObservable = GRH_Without_Vacuity_Guards_from_WeilPositivityObservable

-- --------------------------------------------------------------------------
-- Standard pack skeleton (uniform API).
--
-- Canonical, observer-facing route: positivity only needs to hold on an explicit
-- Observable class of tests, and each nontrivial zero must yield an observable probe.

module QuartetObservable {ℓT ℓW ℓObs : Level} (RS : RiemannSpectral) where
  Assumptions : Set (lsuc (ℓT ⊔ ℓW ⊔ ℓObs))
  Assumptions = WeilPositivityObservable {ℓT} {ℓW} {ℓObs} RS

  Claim : Assumptions → Set
  Claim _ = GRH_Without_Vacuity_Guards RS

  record Pack (A : Assumptions) : Set (lsuc (ℓT ⊔ ℓW ⊔ ℓObs)) where
    field
      claim : Claim A

  mkPack : (A : Assumptions) → Pack A
  mkPack A = record { claim = GRH_Without_Vacuity_Guards_from_WeilPositivityObservable RS A }
