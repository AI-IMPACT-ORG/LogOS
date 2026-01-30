{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.ZetaHasseYonedaLedger where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel
open import LogOS.Kernel.Initial using (InitialKernel)

open import LogOS.Domain.Opacity.NumberTheory.LFunction.RiemannFacts using (RiemannFacts; RiemannSpectralFromFacts)
open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann using (RiemannSpectral)
open import LogOS.Domain.Opacity.NumberTheory.LFunction.ZerosPack using (GRH_Without_Vacuity_Guards)

import LogOS.Theorems.Meta.CommunicableTruth as Comm
import LogOS.Theorems.Meta.MathTruth as MT
import LogOS.Theorems.Meta.ApplicationKit as AppKit
import LogOS.Domain.Opacity.HasseYonedaTransport as HY
import LogOS.Domain.Opacity.WeilCriterionLedger as WCL

-- A compact ledger for the “Hasse regulator + Yoneda transport” route:
-- it exposes exactly the remaining assumptions needed to derive GRH_Without_Vacuity_Guards for a
-- RiemannSpectral adapter produced from `RiemannFacts`.
--
-- This ledger specializes to the Pr-based observability semantics at
-- communicability level ℓW, so “stable truth is observable” is available.

record ZetaHasseYonedaLedger {ℓ ℓW : Level}
                             {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                             (IK : InitialKernel Sig Q)
                             (K  : Kernel Sig Q)
                             (F  : RiemannFacts)
                             : Set (lsuc (lsuc (ℓ ⊔ lsuc ℓW))) where
  private
    RS : RiemannSpectral
    RS = RiemannSpectralFromFacts F

  open RiemannSpectral RS

  field
    -- The predicate on tests/codes used in the weak Weil criterion.
    W-pos : Kernel.Code K → Set ℓW

    -- Weak Weil criterion at the spectral adapter for ζ:
    -- W-pos(probe s) ⇒ OnLine s, for nontrivial zeros s.
    WC : WCL.WeilCriterionWeak RS (MT.TruthPositivity-fromPr {ℓC = ℓW} K W-pos)

    -- Regulator generator, defined canonically in the initial kernel.
    G : HY.HasseGenerator IK

    -- “Stable truth is observable” side conditions for W-pos.
    W-ext    : Comm.DecodeExtensional′ K W-pos
    W-stableBoxBody : ∀ γ → W-pos γ ↔ W-pos (Box K (Kernel.Body K γ))

    -- Finite truth on the regulator-generated tests.
    mkTest-true : ∀ r → W-pos (HY.mkTest {IK = IK} K G r)

    -- Every nontrivial zero’s probe is (up to decoded mutual refinement) one of the
    -- regulator-generated tests.
    sel : ∀ s → NontrivialZero s → HY.Reg G
    mkTest∘sel≈probe
      : ∀ s (nz : NontrivialZero s)
        → HY._≈decode_ K (HY.mkTest {IK = IK} K G (sel s nz))
                        (WCL.WeilCriterionWeak.probe WC s)

  -- End-to-end consequence: GRH_Without_Vacuity_Guards for the induced ζ spectral pack.
  GRH_Without_Vacuity_Guardsζ : GRH_Without_Vacuity_Guards RS
  GRH_Without_Vacuity_Guardsζ =
    HY.GRH_Without_Vacuity_Guards-from-weak-criterion+HasseGenerator-stableTruth
      IK K RS W-pos WC G W-ext W-stableBoxBody mkTest-true sel mkTest∘sel≈probe

-- --------------------------------------------------------------------------
-- Standard pack skeleton (uniform API).

module QuartetZetaHasseYonedaLedger
  {ℓ ℓW : Level}
  {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (IK : InitialKernel Sig Q)
  (K  : Kernel Sig Q)
  (F  : RiemannFacts)
  where

  Assumptions : Set (lsuc (lsuc (ℓ ⊔ lsuc ℓW)))
  Assumptions = ZetaHasseYonedaLedger {ℓ = ℓ} {ℓW = ℓW} IK K F

  Claim : Assumptions → Set
  Claim _ = GRH_Without_Vacuity_Guards (RiemannSpectralFromFacts F)

  module Q =
    AppKit.MakeDerived Assumptions Claim
      (ZetaHasseYonedaLedger.GRH_Without_Vacuity_Guardsζ {F = F})
  open Q public using (Pack; assumptionsOf; claimOf; mkPack)
