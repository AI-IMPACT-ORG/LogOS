{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.Summit.Quantitative where

-- Quantitative summit surface.
--
-- This file only packages the already-landed quantitative capstones:
-- a sharp threshold, a chosen observational Landauer bridge, and least stable
-- multiplicative/renormalised approximations. The critical threshold remains
-- derived from the sharp datum.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con)
open import LogOS.LT.Thin2Cat using (Thin2Cat)

open import LogOS.Ports.CriticalParameter using (CriticalCut; SharpCut)
open import LogOS.Ports.AbstractLandauer.Ledger using (LandauerAssumptions)
open import LogOS.Ports.Opacity.ObservationAction using (ObservationAction)
open import LogOS.Ports.AbstractLandauerObservational using
  ( ObservationalCostBridge )
open import LogOS.Ports.Valuation.AbstractJoinPrequantale using (JoinPrequantale)
open import LogOS.Ports.Valuation.AbstractQuanticNucleus using (QuanticNucleus)
import LogOS.Ports.Valuation.AbstractQuanticNucleus as Nucleus
import LogOS.Ports.Valuation.AbstractConnesKreimer as CK

record QuantitativeSummit
  {ℓTCon ℓTRel ℓP : Level}
  (T : ConPreorder ℓTCon ℓTRel)
  (Good : Con T → Set ℓP)
  {ℓObj ℓHomCon ℓHomRel : Level}
  {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  {ℓObsCon ℓObsRel : Level}
  {ℓScaleCon ℓScaleRel : Level}
  {Scale : ConPreorder ℓScaleCon ℓScaleRel}
  {JP : JoinPrequantale Scale}
  (Obs : ObservationAction {ℓObsCon = ℓObsCon} {ℓObsRel = ℓObsRel} C)
  (L : LandauerAssumptions C Scale JP)
  {ℓLabel : Level}
  (P : Set ℓLabel)
  (N : QuanticNucleus JP)
  : Setω where
  field
    sharpCut : SharpCut T Good
    landauerBridge : ObservationalCostBridge Obs L

    leastStableMultiplicativeApproximation
      : Nucleus.QuanticNucleusLocal.LeastStableMultiplicativeApproximation N

    renormalisedLeastStableApproximation
      : CK.CK.StableConvolutionTheorem JP P N

  criticalCut : CriticalCut T Good
  criticalCut = SharpCut.base sharpCut

quantitativeSummitFromSharpCut
  : ∀ {ℓTCon ℓTRel ℓP : Level}
      {T : ConPreorder ℓTCon ℓTRel}
      {Good : Con T → Set ℓP}
      {ℓObj ℓHomCon ℓHomRel : Level}
      {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
      {ℓObsCon ℓObsRel : Level}
      {ℓScaleCon ℓScaleRel : Level}
      {Scale : ConPreorder ℓScaleCon ℓScaleRel}
      {JP : JoinPrequantale Scale}
      {Obs : ObservationAction {ℓObsCon = ℓObsCon} {ℓObsRel = ℓObsRel} C}
      {L : LandauerAssumptions C Scale JP}
      {ℓLabel : Level}
      {P : Set ℓLabel}
      {N : QuanticNucleus JP}
  → SharpCut T Good
  → ObservationalCostBridge Obs L
  → Nucleus.QuanticNucleusLocal.LeastStableMultiplicativeApproximation N
  → CK.CK.StableConvolutionTheorem JP P N
  → QuantitativeSummit T Good Obs L P N
quantitativeSummitFromSharpCut sharp bridge leastStable renorm =
  record
    { sharpCut = sharp
    ; landauerBridge = bridge
    ; leastStableMultiplicativeApproximation = leastStable
    ; renormalisedLeastStableApproximation = renorm
    }
