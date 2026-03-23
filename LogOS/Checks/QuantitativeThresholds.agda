{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.QuantitativeThresholds where

open import LogOS.Prelude
open import LogOS.Host.Nat using (zero; suc)
open import LogOS.Prelude.Fin using (Fin; fzero; fsuc; _≢_)
open import LogOS.Prelude.Nat.Order using (_≤ℕ_; z≤n; s≤s)
open import LogOS.Syntax.Prop using (_↔_; intro)
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; _≈_; refl⊑)
open import LogOS.LT.ConPreorder.Truth using (TruthPreorder; truthView)
open import LogOS.LT.View using (View; _≈[_]_)
open import LogOS.LT.View.Factorisation using (FactorisesThrough; idFactorisation)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.Ports.CriticalParameter using (CriticalCut; SharpCut)
open import LogOS.Ports.Universality.NatBoundary using (NatBoundary)
open import LogOS.Ports.Opacity.Distinguishability using (ObservedFamily)
open import LogOS.Ports.Opacity.Profile using
  ( ObservationProfile
  ; OpaqueAt
  ; ExactOpacityThreshold
  ; exactOpacityThreshold→sharp
  )
open import LogOS.Ports.Opacity.FiniteCompression using
  ( FiniteCompressionWitness
  ; finiteLossCount
  )
open import LogOS.Ports.AbstractLandauer.Ledger using (LandauerAssumptions)
open import LogOS.Ports.AbstractLandauer2Cat using (CostBound; boundOf; boundProof)
open import LogOS.Ports.Opacity.ObservationAction using
  ( ObservationAction
  ; processFactorisation
  )
open import LogOS.Ports.AbstractLandauerObservational using
  ( ObservationalCostBridge
  ; countLoss≤cost
  ; singleCompression≤cost
  ; compressionValue
  )
open import LogOS.Ports.Valuation.AbstractJoinPrequantale using (JoinPrequantale)
open import LogOS.Ports.Valuation.CompressionValuation using (singleCompression)

data Carrier : Set where
  α β : Carrier

twoPoints : ObservedFamily Carrier
twoPoints =
  record
    { size = suc (suc zero)
    ; at = λ where
        fzero → α
        (fsuc fzero) → β
    }

privateView : View Carrier (TruthPreorder {lzero})
privateView = truthView privateObs
  where
    privateObs : Carrier → Set
    privateObs α = ⊤
    privateObs β = ⊥

opaqueView : View Carrier (TruthPreorder {lzero})
opaqueView = truthView (λ _ → ⊤)

collapseToOpaque
  : FactorisesThrough privateView opaqueView
collapseToOpaque =
  record
    { collapse = λ _ → ⊤
    ; collapse-mono = λ _ _ → tt
    ; commute = λ where
        α → (λ _ → tt) , (λ _ → tt)
        β → (λ _ → tt) , (λ _ → tt)
    }

toyProfile : ObservationProfile Carrier NatBoundary
toyProfile =
  record
    { O = λ _ → TruthPreorder {lzero}
    ; observe = λ where
        zero → privateView
        (suc _) → opaqueView
    ; weaken = λ where
        {zero} {zero} z≤n → idFactorisation privateView
        {zero} {suc _} z≤n → collapseToOpaque
        {suc _} {suc _} (s≤s _) → idFactorisation opaqueView
    }

exactOpacityThreshold
  : ExactOpacityThreshold toyProfile twoPoints (suc zero)
exactOpacityThreshold zero =
  intro
    opaqueAtZero→cut
    (λ ())
  where
    opaqueAtZero→cut : OpaqueAt toyProfile twoPoints zero → suc zero ≤ℕ zero
    opaqueAtZero→cut ((fzero , fzero) , (distinct , _)) = ⊥-elim (distinct refl)
    opaqueAtZero→cut ((fzero , fsuc fzero) , (_ , collapsed)) = ⊥-elim (fst collapsed tt)
    opaqueAtZero→cut ((fsuc fzero , fzero) , (_ , collapsed)) = ⊥-elim (snd collapsed tt)
    opaqueAtZero→cut ((fsuc fzero , fsuc fzero) , (distinct , _)) = ⊥-elim (distinct refl)
exactOpacityThreshold (suc t) =
  intro
    (λ _ → s≤s z≤n)
    (λ _ → ((fzero , fsuc fzero) , ((λ ()) , ((λ _ → tt) , (λ _ → tt)))))

sharpOpacityCut
  : SharpCut NatBoundary (OpaqueAt toyProfile twoPoints)
sharpOpacityCut =
  exactOpacityThreshold→sharp
    {T = NatBoundary}
    {P = toyProfile}
    {S = twoPoints}
    exactOpacityThreshold

criticalOpacityCut
  : CriticalCut NatBoundary (OpaqueAt toyProfile twoPoints)
criticalOpacityCut =
  SharpCut.base sharpOpacityCut

_ : Con NatBoundary
_ = CriticalCut.Λ criticalOpacityCut

_ : CriticalCut NatBoundary (OpaqueAt toyProfile twoPoints)
_ = SharpCut.base sharpOpacityCut

module LandauerBridgeWitness
  {ℓObj ℓHomCon ℓHomRel ℓObsCon ℓObsRel ℓScaleCon ℓScaleRel : Level}
  {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  {Scale : ConPreorder ℓScaleCon ℓScaleRel}
  {JP : JoinPrequantale Scale}
  {Obs : ObservationAction {ℓObsCon = ℓObsCon} {ℓObsRel = ℓObsRel} C}
  {L : LandauerAssumptions C Scale JP}
  (Bridge : ObservationalCostBridge Obs L)
  {A B : Thin2Cat.Obj C}
  {h : Con (Thin2Cat.Hom C A B)}
  (fc : FiniteCompressionWitness (processFactorisation Obs h))
  (cb : CostBound L h)
  where

  _ : _⊑_ Scale (compressionValue Bridge (finiteLossCount fc)) (LandauerAssumptions.cost L h)
  _ = countLoss≤cost Bridge fc

  _ : _⊑_ Scale (compressionValue Bridge (finiteLossCount fc)) (boundOf cb)
  _ =
    let
      module R = LogOS.Prelude.RefinementKit.Reasoning Scale
      open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
    in
    begin⊑
      compressionValue Bridge (finiteLossCount fc)
        ⊑⟨ countLoss≤cost Bridge fc ⟩
      LandauerAssumptions.cost L h
        ⊑⟨ boundProof cb ⟩
      boundOf cb ∎⊑

  _ : _⊑_ Scale (singleCompression (ObservationalCostBridge.valuation Bridge)) (LandauerAssumptions.cost L h)
  _ = singleCompression≤cost Bridge fc

  _ : _⊑_ Scale (singleCompression (ObservationalCostBridge.valuation Bridge)) (boundOf cb)
  _ =
    let
      module R = LogOS.Prelude.RefinementKit.Reasoning Scale
      open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
    in
    begin⊑
      singleCompression (ObservationalCostBridge.valuation Bridge)
        ⊑⟨ singleCompression≤cost Bridge fc ⟩
      LandauerAssumptions.cost L h
        ⊑⟨ boundProof cb ⟩
      boundOf cb ∎⊑
