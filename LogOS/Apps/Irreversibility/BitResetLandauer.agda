{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.Irreversibility.BitResetLandauer where

-- Landauer lower-bound bridge for the bit reset example.
--
-- The observation lives on the causal/local physical base, not on the Deutsch
-- stack. A bridge assumption then turns opacity/compression-derived finite
-- loss into a lower bound on the actual cost, with chosen `CostBound`s as a
-- derived corollary.

open import LogOS.Prelude
open import LogOS.Host.Nat using (ℕ; zero; suc)
open import LogOS.LT.ConPreorder using (_⊑_)

open import LogOS.Ports.AbstractLandauer.Ledger using (LandauerAssumptions)
open import LogOS.Ports.AbstractLandauer2Cat using (CostBound; boundOf; boundProof)
open import LogOS.Ports.Valuation.ScaleBoundary using (ScaleBoundary)
open import LogOS.Ports.Valuation.AbstractJoinPrequantale using (ScaleJoinPrequantale)
open import LogOS.Ports.Valuation.NatQAdapter using (natQAdapter)
open import LogOS.Ports.Valuation.CompressionValuation using (singleCompression)
open import LogOS.Ports.Opacity.ObservationAction using
  ( ProcessObservation
  ; processFactorisationAt
  )
open import LogOS.Ports.Opacity.FiniteCompression using
  ( FiniteCompressionWitness
  ; finiteLossCount
  )
open import LogOS.Ports.AbstractLandauerObservational using
  ( FixedObservationalCostBridge
  ; fixedCompressionValue
  ; singleCompression≤fixedCost
  )

import LogOS.Apps.Irreversibility.BitReset as BitReset
import LogOS.Apps.Irreversibility.BitResetCompression as BitResetCompression
import LogOS.Apps.Irreversibility.BitResetDeutsch as BitResetDeutsch

Scale = ScaleBoundary natQAdapter
JP = ScaleJoinPrequantale natQAdapter

resetObservation
  : ProcessObservation
      {C = BitResetDeutsch.Cau.WithPort}
      {A = BitResetDeutsch.bitCausalObj}
      {B = BitResetDeutsch.bitCausalObj}
      BitResetDeutsch.resetCausal
resetObservation =
  record
    { ObsSrc = BitReset.BitPreorder
    ; ObsTgt = BitReset.BitPreorder
    ; act = BitReset.resetBoundary
    ; act-mono = BitResetCompression.resetBoundary-mono
    }

resetFiniteCompression
  : FiniteCompressionWitness (processFactorisationAt resetObservation)
resetFiniteCompression =
  BitResetCompression.bitResetFiniteCompression

ResetBridge
  : LandauerAssumptions BitResetDeutsch.Cau.WithPort Scale JP
  → Set _
ResetBridge L =
  FixedObservationalCostBridge
    {C = BitResetDeutsch.Cau.WithPort}
    {A = BitResetDeutsch.bitCausalObj}
    {B = BitResetDeutsch.bitCausalObj}
    {h = BitResetDeutsch.resetCausal}
    resetObservation
    L

resetCompressionValue
  : ∀ {L : LandauerAssumptions BitResetDeutsch.Cau.WithPort Scale JP}
  → ResetBridge L
  → ℕ → Refinement.Con Scale
resetCompressionValue {L} =
  fixedCompressionValue
    {C = BitResetDeutsch.Cau.WithPort}
    {A = BitResetDeutsch.bitCausalObj}
    {B = BitResetDeutsch.bitCausalObj}
    {h = BitResetDeutsch.resetCausal}
    {Obs = resetObservation}
    {L = L}

resetCountLoss≤cost
  : ∀ {L : LandauerAssumptions BitResetDeutsch.Cau.WithPort Scale JP}
  → (Bridge : ResetBridge L)
  → _⊑_ Scale
      (resetCompressionValue Bridge (finiteLossCount resetFiniteCompression))
      (LandauerAssumptions.cost L BitResetDeutsch.resetCausal)
resetCountLoss≤cost {L} Bridge =
  FixedObservationalCostBridge.countLoss≤fixedCost
    {C = BitResetDeutsch.Cau.WithPort}
    {A = BitResetDeutsch.bitCausalObj}
    {B = BitResetDeutsch.bitCausalObj}
    {h = BitResetDeutsch.resetCausal}
    {Obs = resetObservation}
    {L = L}
    Bridge
    resetFiniteCompression

resetSingleCompression≤cost
  : ∀ {L : LandauerAssumptions BitResetDeutsch.Cau.WithPort Scale JP}
  → (Bridge : ResetBridge L)
  → _⊑_ Scale
      (singleCompression (FixedObservationalCostBridge.valuation Bridge))
      (LandauerAssumptions.cost L BitResetDeutsch.resetCausal)
resetSingleCompression≤cost {L} Bridge =
  singleCompression≤fixedCost
    {C = BitResetDeutsch.Cau.WithPort}
    {A = BitResetDeutsch.bitCausalObj}
    {B = BitResetDeutsch.bitCausalObj}
    {h = BitResetDeutsch.resetCausal}
    {Obs = resetObservation}
    {L = L}
    Bridge
    resetFiniteCompression

module UsingBridge
  (L : LandauerAssumptions BitResetDeutsch.Cau.WithPort Scale JP)
  (Bridge : ResetBridge L)
  where

  resetCostLowerBound
    : _⊑_ Scale
        (resetCompressionValue Bridge (finiteLossCount resetFiniteCompression))
        (LandauerAssumptions.cost L BitResetDeutsch.resetCausal)
  resetCostLowerBound =
    resetCountLoss≤cost Bridge

  resetLowerBound
    : (resetCostBound : CostBound L BitResetDeutsch.resetCausal)
    → _⊑_ Scale
        (resetCompressionValue Bridge (finiteLossCount resetFiniteCompression))
        (boundOf resetCostBound)
  resetLowerBound resetCostBound =
    let
      module R = LogOS.Prelude.RefinementKit.Reasoning Scale
      open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
    in
    begin⊑
      resetCompressionValue Bridge (finiteLossCount resetFiniteCompression)
        ⊑⟨ resetCountLoss≤cost Bridge ⟩
      LandauerAssumptions.cost L BitResetDeutsch.resetCausal
        ⊑⟨ boundProof resetCostBound ⟩
      boundOf resetCostBound ∎⊑

  resetSingleCompressionCostLowerBound
    : _⊑_ Scale (suc zero) (singleCompression (FixedObservationalCostBridge.valuation Bridge))
    → _⊑_ Scale (suc zero) (LandauerAssumptions.cost L BitResetDeutsch.resetCausal)
  resetSingleCompressionCostLowerBound singleCompression≥1 =
    let
      module R = LogOS.Prelude.RefinementKit.Reasoning Scale
      open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
    in
    begin⊑
      suc zero
        ⊑⟨ singleCompression≥1 ⟩
      singleCompression (FixedObservationalCostBridge.valuation Bridge)
        ⊑⟨ resetSingleCompression≤cost Bridge ⟩
      LandauerAssumptions.cost L BitResetDeutsch.resetCausal ∎⊑

  resetSingleCompressionBoundLowerBound
    : _⊑_ Scale (suc zero) (singleCompression (FixedObservationalCostBridge.valuation Bridge))
    → (resetCostBound : CostBound L BitResetDeutsch.resetCausal)
    → _⊑_ Scale (suc zero) (boundOf resetCostBound)
  resetSingleCompressionBoundLowerBound singleCompression≥1 resetCostBound =
    let
      module R = LogOS.Prelude.RefinementKit.Reasoning Scale
      open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
    in
    begin⊑
      suc zero
        ⊑⟨ resetSingleCompressionCostLowerBound singleCompression≥1 ⟩
      LandauerAssumptions.cost L BitResetDeutsch.resetCausal
        ⊑⟨ boundProof resetCostBound ⟩
      boundOf resetCostBound ∎⊑
