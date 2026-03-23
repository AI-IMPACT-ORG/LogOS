{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.AbstractLandauerObservational where

-- Explicit, axiomatic bridge from the opacity pack's finite-loss layer to
-- actual Landauer costs.
--
-- This module does not derive thermodynamic cost from observational collapse
-- alone. Instead it packages the minimal additional assumptions currently used:
-- a chosen calibrated interpretation of finite loss counts into the ambient
-- cost prequantale, together with a chosen axiom stating that those interpreted
-- counts lower-bound actual cost.
--
-- Chosen displayed `CostBound` corollaries are obtained by composing the
-- consequences below with `boundProof`, rather than carried as a parallel API.

open import LogOS.Prelude
open import LogOS.Host.Nat using (ℕ)
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.Ports.Opacity.FiniteCompression using
  ( FiniteCompressionWitness
  ; finiteLossCount
  ; finiteLossCount-atLeastOne
  )
open import LogOS.Ports.Opacity.ObservationAction using
  ( ObservationAction
  ; ProcessObservation
  ; processFactorisation
  ; processFactorisationAt
  )

open import LogOS.Ports.AbstractLandauer.Ledger using (LandauerAssumptions)
open import LogOS.Ports.Valuation.AbstractJoinPrequantale using (JoinPrequantale)
open import LogOS.Ports.Valuation.CompressionValuation using
  ( CompressionValuation
  ; countValue
  ; singleCompression
  ; singleCompression≤countValue
  )

record ObservationalCostBridge
  {ℓObj ℓHomCon ℓHomRel ℓObsCon ℓObsRel ℓScaleCon ℓScaleRel : Level}
  {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  {Scale : ConPreorder ℓScaleCon ℓScaleRel}
    {JP : JoinPrequantale Scale}
  (Obs : ObservationAction {ℓObsCon = ℓObsCon} {ℓObsRel = ℓObsRel} C)
  (L : LandauerAssumptions C Scale JP)
  : Set
      (lsuc
        (ℓObj ⊔ ℓHomCon ⊔ ℓHomRel ⊔ ℓObsCon ⊔ ℓObsRel ⊔ ℓScaleCon ⊔ ℓScaleRel))
  where
  field
    valuation : CompressionValuation JP

    countLoss≤cost
      : ∀ {A B}
        {h : Con (Thin2Cat.Hom C A B)}
      → (fc : FiniteCompressionWitness (processFactorisation Obs h))
      → _⊑_ Scale
          (countValue valuation (finiteLossCount fc))
          (LandauerAssumptions.cost L h)

open ObservationalCostBridge public

compressionValue
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓObsCon ℓObsRel ℓScaleCon ℓScaleRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {Scale : ConPreorder ℓScaleCon ℓScaleRel}
    {JP : JoinPrequantale Scale}
    {Obs : ObservationAction {ℓObsCon = ℓObsCon} {ℓObsRel = ℓObsRel} C}
    {L : LandauerAssumptions C Scale JP}
  → ObservationalCostBridge Obs L
  → ℕ → Con Scale
compressionValue B =
  countValue (valuation B)

singleCompression≤cost
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓObsCon ℓObsRel ℓScaleCon ℓScaleRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {Scale : ConPreorder ℓScaleCon ℓScaleRel}
    {JP : JoinPrequantale Scale}
    {Obs : ObservationAction {ℓObsCon = ℓObsCon} {ℓObsRel = ℓObsRel} C}
    {L : LandauerAssumptions C Scale JP}
  → (B : ObservationalCostBridge Obs L)
  → ∀ {A B₀} {h : Con (Thin2Cat.Hom C A B₀)}
  → (fc : FiniteCompressionWitness (processFactorisation Obs h))
  → _⊑_ Scale (singleCompression (valuation B)) (LandauerAssumptions.cost L h)
singleCompression≤cost {Scale = Scale} {Obs = Obs} {L = L} B {h = h} fc =
  let
    module R = LogOS.Prelude.RefinementKit.Reasoning Scale
    open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
  in
  begin⊑
    singleCompression (valuation B)
      ⊑⟨ singleCompression≤countValue
            (valuation B)
            {n = finiteLossCount {F = processFactorisation Obs h} fc}
            (finiteLossCount-atLeastOne {F = processFactorisation Obs h} fc) ⟩
    compressionValue B (finiteLossCount {F = processFactorisation Obs h} fc)
      ⊑⟨ countLoss≤cost B fc ⟩
    LandauerAssumptions.cost L h ∎⊑

record FixedObservationalCostBridge
  {ℓObj ℓHomCon ℓHomRel ℓObsCon ℓObsRel ℓScaleCon ℓScaleRel : Level}
  {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  {A B : Thin2Cat.Obj C}
  {h : Con (Thin2Cat.Hom C A B)}
  {Scale : ConPreorder ℓScaleCon ℓScaleRel}
    {JP : JoinPrequantale Scale}
  (Obs : ProcessObservation {ℓObsCon = ℓObsCon} {ℓObsRel = ℓObsRel} {C = C} {A = A} {B = B} h)
  (L : LandauerAssumptions C Scale JP)
  : Set
      (lsuc
        (ℓObj ⊔ ℓHomCon ⊔ ℓHomRel ⊔ ℓObsCon ⊔ ℓObsRel ⊔ ℓScaleCon ⊔ ℓScaleRel))
  where
  field
    valuation : CompressionValuation JP

    countLoss≤fixedCost
      : (fc : FiniteCompressionWitness (processFactorisationAt Obs))
      → _⊑_ Scale
          (countValue valuation (finiteLossCount fc))
          (LandauerAssumptions.cost L h)

fixedCompressionValue
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓObsCon ℓObsRel ℓScaleCon ℓScaleRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {A B : Thin2Cat.Obj C}
    {h : Con (Thin2Cat.Hom C A B)}
    {Scale : ConPreorder ℓScaleCon ℓScaleRel}
    {JP : JoinPrequantale Scale}
    {Obs : ProcessObservation {ℓObsCon = ℓObsCon} {ℓObsRel = ℓObsRel} {C = C} {A = A} {B = B} h}
    {L : LandauerAssumptions C Scale JP}
  → FixedObservationalCostBridge {C = C} {A = A} {B = B} {h = h} Obs L
  → ℕ → Con Scale
fixedCompressionValue B =
  countValue (FixedObservationalCostBridge.valuation B)

singleCompression≤fixedCost
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓObsCon ℓObsRel ℓScaleCon ℓScaleRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {A B : Thin2Cat.Obj C}
    {h : Con (Thin2Cat.Hom C A B)}
    {Scale : ConPreorder ℓScaleCon ℓScaleRel}
    {JP : JoinPrequantale Scale}
    {Obs : ProcessObservation {ℓObsCon = ℓObsCon} {ℓObsRel = ℓObsRel} {C = C} {A = A} {B = B} h}
    {L : LandauerAssumptions C Scale JP}
  → (Bdg : FixedObservationalCostBridge {C = C} {A = A} {B = B} {h = h} Obs L)
  → (fc : FiniteCompressionWitness (processFactorisationAt Obs))
  → _⊑_ Scale
      (singleCompression (FixedObservationalCostBridge.valuation Bdg))
      (LandauerAssumptions.cost L h)
singleCompression≤fixedCost {Scale = Scale} {Obs = Obs} {L = L} Bdg fc =
  let
    module R = LogOS.Prelude.RefinementKit.Reasoning Scale
    open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
  in
  begin⊑
    singleCompression (FixedObservationalCostBridge.valuation Bdg)
      ⊑⟨ singleCompression≤countValue
            (FixedObservationalCostBridge.valuation Bdg)
            {n = finiteLossCount {F = processFactorisationAt Obs} fc}
            (finiteLossCount-atLeastOne {F = processFactorisationAt Obs} fc) ⟩
    fixedCompressionValue Bdg (finiteLossCount {F = processFactorisationAt Obs} fc)
      ⊑⟨ FixedObservationalCostBridge.countLoss≤fixedCost Bdg fc ⟩
    LandauerAssumptions.cost L _ ∎⊑
