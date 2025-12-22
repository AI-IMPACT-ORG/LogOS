{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.Applications.GRH.Systems where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

open import LogOS.Domain.Opacity.NumberTheory.HP.Interface as HPi

open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann
open import LogOS.Domain.Opacity.Applications.GRH.ZetaBridge
open import LogOS.Domain.Opacity.Applications.GRH.HPGRHLimit as HPLimit
import LogOS.Domain.Opacity.TruthSeparation as TruthSep
open TruthSep using (RStoSP)
open import LogOS.Domain.Opacity.PNTBridge as PNT
import LogOS.Domain.Opacity.WeilPositivityBridge as WeilPos
open import LogOS.Theorems.Meta.GRHBridge as GRHB

-- One-line "systems" wrappers that present conditional GRH theorems
-- for operator (HP) and categorical (nucleus) bridges.

GRH_Without_Vacuity_Guards_HPFinite
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K   : Kernel Sig Q)
    (HP  : HPi.HPInterface K)
    (EF  : HPi.EmbedFaithful K HP)
    (RS  : RiemannSpectral)
    (B   : ZetaOpBridgeFinite Sig Q K HP RS)
  → ∀ s → RiemannSpectral.NontrivialZero RS s → RiemannSpectral.OnLine RS s
GRH_Without_Vacuity_Guards_HPFinite K HP EF RS B = GRH_Without_Vacuity_Guards_from_finite K HP EF RS B

GRH_Without_Vacuity_Guards_HP∞
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K   : Kernel Sig Q)
    (AHP : HPLimit.ApproxHP Sig Q K)
    (RS  : RiemannSpectral)
    (B   : ZetaOpBridgeLimit Sig Q K AHP RS)
    (i   : HPLimit.ResIdx.I (HPLimit.ApproxHP.idx AHP))
  → ∀ s → RiemannSpectral.NontrivialZero RS s → RiemannSpectral.OnLine RS s
GRH_Without_Vacuity_Guards_HP∞ K AHP RS B i = GRH_Without_Vacuity_Guards_from_limit K AHP RS B i

GRH_Without_Vacuity_Guards_Nucleus
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K   : Kernel Sig Q)
    (RS  : RiemannSpectral)
    (GN  : GRHB.GlobalNucleusBridge K (RStoSP RS))
  → ∀ s → RiemannSpectral.NontrivialZero RS s → RiemannSpectral.OnLine RS s
GRH_Without_Vacuity_Guards_Nucleus K RS GN = GRHB.GRH_Without_Vacuity_Guards_via_GlobalNucleus K (RStoSP RS) GN

GRH_Without_Vacuity_Guards_Nucleus∞
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K   : Kernel Sig Q)
    (RS  : RiemannSpectral)
    {Idx : Set}
    (GL  : GRHB.GlobalNucleusLimit K (RStoSP RS) Idx)
  → ∀ s → RiemannSpectral.NontrivialZero RS s → RiemannSpectral.OnLine RS s
GRH_Without_Vacuity_Guards_Nucleus∞ K RS {Idx} GL = GRHB.GRH_Without_Vacuity_Guards_via_GlobalNucleus∞ K (RStoSP RS) GL

-- PNT as stability (observer-facing): if a model supplies a local closure
-- sandwiched by Flow and a boundary constraint encoding the PNT statement,
-- then local fixedness transports to global Flow fixedness, yielding PNT.

PNT_from_TruthSeparation
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K   : Kernel Sig Q)
    (RS  : RiemannSpectral)
    (Sep : TruthSep.GlobalTruthSeparation K RS)
    (PB  : PNT.PNTFromGlobalTruthSeparation K RS Sep)
  → PNT.PNTFromGlobalTruthSeparation.PNT PB
PNT_from_TruthSeparation K RS Sep PB = PNT.PNTFromGlobalTruthSeparation.PNT-from-separation PB

-- RH/GRH via Weil's criterion (operator-free, schematic): a global positivity
-- predicate on tests plus a ζ-specific probe lemma yields the OnLine clause.

GRH_Without_Vacuity_Guards_WeilPositivity
  : ∀ {ℓT ℓW}
    (RS : RiemannSpectral)
    (A  : WeilPos.WeilPositivityAssumptions {ℓT} {ℓW} RS)
  → ∀ s → RiemannSpectral.NontrivialZero RS s → RiemannSpectral.OnLine RS s
GRH_Without_Vacuity_Guards_WeilPositivity RS A = WeilPos.GRH_Without_Vacuity_Guards_from_WeilPositivity RS A

GRH_Without_Vacuity_Guards_WeilPositivityObservable
  : ∀ {ℓT ℓW ℓObs}
    (RS : RiemannSpectral)
    (A  : WeilPos.WeilPositivityObservable {ℓT} {ℓW} {ℓObs} RS)
  → ∀ s → RiemannSpectral.NontrivialZero RS s → RiemannSpectral.OnLine RS s
GRH_Without_Vacuity_Guards_WeilPositivityObservable RS A = WeilPos.GRH_Without_Vacuity_Guards_from_WeilPositivityObservable RS A
