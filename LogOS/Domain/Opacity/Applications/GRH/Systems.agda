{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.Applications.GRH.Systems where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Closure using (ClosureOp)
open import LogOS.Minimal.Con
open import LogOS.Kernel
open import LogOS.Kernel.Initial using (InitialKernel)

open import LogOS.Domain.Opacity.NumberTheory.HP.Interface as HPi

open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann
open import LogOS.Domain.Opacity.Applications.GRH.ZetaBridge
open import LogOS.Domain.Opacity.Applications.GRH.HPGRHLimit as HPLimit
import LogOS.Domain.Opacity.TruthSeparation as TruthSep
import LogOS.Domain.Opacity.TruthSeparationForcing as TruthSepF
open TruthSep using (RStoSP)
open import LogOS.Domain.Opacity.PNTBridge as PNT
import LogOS.Domain.Opacity.Meaningfulness as Meaning
import LogOS.Domain.Opacity.GRHLedger as GRH
import LogOS.Domain.Opacity.WeilPositivityBridge as WeilPos
import LogOS.Domain.Opacity.AccessibleWeilLedger as AWL
import LogOS.Domain.Opacity.AccessibleWeilMeetLimitBridgeStable as AWMLS
import LogOS.Domain.Opacity.AccessibleWeilMeetLimitBridgeStableCofinal as AWMLSC
import LogOS.Domain.Opacity.ZetaAccessibleMeetLimitLedgerStable as ZAMLS
import LogOS.Domain.Opacity.ZetaHasseYonedaLedger as ZHY
open import LogOS.Theorems.Meta.GRHBridge as GRHB

open import LogOS.Domain.Opacity.NumberTheory.LFunction.RiemannFacts using (RiemannFacts; RiemannSpectralFromFacts)

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

GRH_Without_Vacuity_Guards_Forcing
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K   : Kernel Sig Q)
    (RS  : RiemannSpectral)
    (J   : ClosureOp (BulkBoundary.bnd (Kernel.BB K)))
    (Sep : TruthSepF.ProperForcingTruthSeparation K RS J)
  → ∀ s → RiemannSpectral.NontrivialZero RS s → RiemannSpectral.OnLine RS s
GRH_Without_Vacuity_Guards_Forcing K RS J Sep =
  TruthSepF.GRH_Without_Vacuity_Guards_from_ProperForcingTruthSeparation K RS J Sep

-- PNT as stability (observer-facing): if a model supplies a Flow-based
-- separation witness and a boundary constraint encoding the PNT statement,
-- then closure stability yields PNT.

PNT_from_FlowTruthSeparation
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K   : Kernel Sig Q)
    (RS  : RiemannSpectral)
    (Sep : TruthSep.FlowTruthSeparation K RS)
    (PB  : PNT.PNTFromFlowTruthSeparation K RS Sep)
  → PNT.PNTFromForcingTruthSeparation.PNT PB
PNT_from_FlowTruthSeparation K RS Sep PB = PNT.PNTFromForcingTruthSeparation.PNT-from-separation PB

PNT_from_ForcingTruthSeparation
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K   : Kernel Sig Q)
    (RS  : RiemannSpectral)
    (J   : ClosureOp (BulkBoundary.bnd (Kernel.BB K)))
    (Sep : TruthSepF.ForcingTruthSeparation K RS J)
    (PB  : PNT.PNTFromForcingTruthSeparation K RS J Sep)
  → PNT.PNTFromForcingTruthSeparation.PNT PB
PNT_from_ForcingTruthSeparation K RS J Sep PB =
  PNT.PNTFromForcingTruthSeparation.PNT-from-separation PB

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

GRH_WeilPositivity
  : ∀ {ℓT ℓW}
    (RS : RiemannSpectral)
    (A  : WeilPos.WeilPositivityAssumptions {ℓT} {ℓW} RS)
    (guards : Meaning.VacuityGuards RS)
  → GRH.GRH RS
GRH_WeilPositivity RS A guards = WeilPos.GRH_from_WeilPositivity RS A guards

GRH_WeilPositivityObservable
  : ∀ {ℓT ℓW ℓObs}
    (RS : RiemannSpectral)
    (A  : WeilPos.WeilPositivityObservable {ℓT} {ℓW} {ℓObs} RS)
    (guards : Meaning.VacuityGuards RS)
  → GRH.GRH RS
GRH_WeilPositivityObservable RS A guards =
  WeilPos.GRH_from_WeilPositivityObservable RS A guards

-- Kernel-driven strengthenings for the Weil/explicit-formula route:
-- replace probe-observability assumptions with Pr-derived observability for
-- stable/extensional predicates, plus meet-limit/cofinal/Yoneda coverage packs.

GRH_Without_Vacuity_Guards_AccessibleStableTruth
  : ∀ {ℓ ℓW} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (RS : RiemannSpectral)
    (B  : AWL.AccessibleWeilLedgerRSStableTruth {ℓ = ℓ} {ℓW = ℓW} K RS)
  → ∀ s → RiemannSpectral.NontrivialZero RS s → RiemannSpectral.OnLine RS s
GRH_Without_Vacuity_Guards_AccessibleStableTruth K RS B =
  AWL.AccessibleWeilLedgerRSStableTruth.GRH_Without_Vacuity_Guards-from-stableTruth-ledger B

GRH_Without_Vacuity_Guards_ZetaStableTruth
  : ∀ {ℓ ℓW} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (F : RiemannFacts)
    (L : AWL.AccessibleWeilLedgerStableTruth {ℓ = ℓ} {ℓW = ℓW} K F)
  → ∀ s → RiemannSpectral.NontrivialZero (RiemannSpectralFromFacts F) s
        → RiemannSpectral.OnLine (RiemannSpectralFromFacts F) s
GRH_Without_Vacuity_Guards_ZetaStableTruth K F L =
  AWL.AccessibleWeilLedgerStableTruth.GRH_Without_Vacuity_Guardsζ L

GRH_Without_Vacuity_Guards_AccessibleMeetLimitStable
  : ∀ {ℓ ℓW} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (RS : RiemannSpectral)
    (B  : AWMLS.AccessibleWeilMeetLimitBridgeStable {ℓ = ℓ} {ℓW = ℓW} K RS)
  → ∀ s → RiemannSpectral.NontrivialZero RS s → RiemannSpectral.OnLine RS s
GRH_Without_Vacuity_Guards_AccessibleMeetLimitStable K RS B =
  AWMLS.AccessibleWeilMeetLimitBridgeStable.GRH_Without_Vacuity_Guards-from-stable-bridge B

GRH_Without_Vacuity_Guards_AccessibleMeetLimitStableCofinal
  : ∀ {ℓ ℓW} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (RS : RiemannSpectral)
    (B  : AWMLSC.AccessibleWeilMeetLimitBridgeStableCofinal {ℓ = ℓ} {ℓW = ℓW} K RS)
  → ∀ s → RiemannSpectral.NontrivialZero RS s → RiemannSpectral.OnLine RS s
GRH_Without_Vacuity_Guards_AccessibleMeetLimitStableCofinal K RS B =
  AWMLSC.AccessibleWeilMeetLimitBridgeStableCofinal.GRH_Without_Vacuity_Guards-from-cofinal B

GRH_Without_Vacuity_Guards_ZetaMeetLimitStable
  : ∀ {ℓ ℓW} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (F : RiemannFacts)
    (L : ZAMLS.ZetaAccessibleMeetLimitLedgerStable {ℓ = ℓ} {ℓW = ℓW} K F)
  → ∀ s → RiemannSpectral.NontrivialZero (RiemannSpectralFromFacts F) s
        → RiemannSpectral.OnLine (RiemannSpectralFromFacts F) s
GRH_Without_Vacuity_Guards_ZetaMeetLimitStable K F L =
  ZAMLS.ZetaAccessibleMeetLimitLedgerStable.GRH_Without_Vacuity_Guardsζ L

GRH_Without_Vacuity_Guards_ZetaHasseYoneda
  : ∀ {ℓ ℓW} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (IK : InitialKernel Sig Q)
    (K  : Kernel Sig Q)
    (F  : RiemannFacts)
    (L  : ZHY.ZetaHasseYonedaLedger {ℓ = ℓ} {ℓW = ℓW} IK K F)
  → ∀ s → RiemannSpectral.NontrivialZero (RiemannSpectralFromFacts F) s
        → RiemannSpectral.OnLine (RiemannSpectralFromFacts F) s
GRH_Without_Vacuity_Guards_ZetaHasseYoneda IK K F L =
  ZHY.ZetaHasseYonedaLedger.GRH_Without_Vacuity_Guardsζ L
