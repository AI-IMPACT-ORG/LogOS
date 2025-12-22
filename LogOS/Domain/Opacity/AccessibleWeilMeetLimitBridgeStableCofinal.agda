{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.AccessibleWeilMeetLimitBridgeStableCofinal where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)
open import Data.Product using (Σ; _,_; proj₁; proj₂)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

import LogOS.Theorems.Meta.CommunicableTruth as Comm
import LogOS.Theorems.Meta.MathTruth as MT
import LogOS.Theorems.Meta.LimitPublicisation as LP

open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann using (RiemannSpectral)
open import LogOS.Domain.Opacity.NumberTheory.LFunction.ZerosPack using (GRH_Without_Vacuity_Guards)

import LogOS.Domain.Opacity.AccessibleWeilMeetLimitBridgeStable as Stable
import LogOS.Domain.Opacity.AccessibleWeilMeetLimitBridge as AWLM

open import LogOS.Helpers.LocalGlobalBoundary as LGB

-- Cofinal-schedule refinement of the stable meet-limit bridge:
-- instead of requiring probe truth at every regulator index, it suffices to give
-- probe truth along a cofinal regulator schedule (e.g. an ω-chain n ↦ rₙ).

record AccessibleWeilMeetLimitBridgeStableCofinal {ℓ ℓW : Level}
                                                  {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                                                  (K  : Kernel Sig Q)
                                                  (RS : RiemannSpectral)
                                                  : Set (lsuc (ℓ ⊔ lsuc ℓW)) where
  open RiemannSpectral RS

  field
    Reg : MT.MathTruth {ℓ} {ℓW} {ℓW} K

  open MT.MathTruth Reg public
    renaming (Idx to Idx; Truthᵢ to Wᵢ; Truth∞ to W∞)

  field
    -- Index order and antitonicity (needed for cofinality transport).
    PIdx : LP.Preorder Idx
    antiMono : ∀ {i j} → LP.Preorder._≤_ PIdx i j → ∀ {γ} → Wᵢ j γ → Wᵢ i γ

    -- Cofinal schedule u : B → Idx (regulator independence).
    B   : Set
    u   : B → Idx
    cof : LP.Cofinal PIdx u

    -- Weil direction at the meet-limit predicate.
    WProbe : AWLM.WeilProbeImplication RS (Kernel.Code K) W∞

    -- Each regulator predicate is stable/extensional (so it is self-observable).
    Wᵢ-ext : ∀ i → Comm.DecodeExtensional′ K (Wᵢ i)
    Wᵢ-stable : ∀ i γ → (Wᵢ i γ) ↔ (Wᵢ i (FlowCode K γ))

    -- Plain finite evidence only along the cofinal schedule.
    holdsᵇ : ∀ b s → NontrivialZero s → Wᵢ (u b) (AWLM.WeilProbeImplication.probe WProbe s)

  -- Derive full “all regulators” evidence from cofinality + antitonicity.
  holdsᵢ : ∀ i s → NontrivialZero s → Wᵢ i (AWLM.WeilProbeImplication.probe WProbe s)
  holdsᵢ i s nz =
    LGB.meetFromCofinal PIdx u cof Wᵢ antiMono (λ b → holdsᵇ b s nz) i

  -- Package the full stable bridge and conclude GRH.
  Bridge : Stable.AccessibleWeilMeetLimitBridgeStable {ℓ = ℓ} {ℓW = ℓW} K RS
  Bridge = record
    { Reg       = Reg
    ; WProbe    = WProbe
    ; Wᵢ-ext    = Wᵢ-ext
    ; Wᵢ-stable = Wᵢ-stable
    ; holdsᵢ    = holdsᵢ
    }

  GRH_Without_Vacuity_Guards-from-cofinal : GRH_Without_Vacuity_Guards RS
  GRH_Without_Vacuity_Guards-from-cofinal =
    Stable.AccessibleWeilMeetLimitBridgeStable.GRH_Without_Vacuity_Guards-from-stable-bridge Bridge

-- --------------------------------------------------------------------------
-- Standard pack skeleton (uniform API).

module QuartetMeetLimitStableCofinal
  {ℓ ℓW}
  {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K  : Kernel Sig Q)
  (RS : RiemannSpectral)
  where

  Assumptions : Set (lsuc (ℓ ⊔ lsuc ℓW))
  Assumptions = AccessibleWeilMeetLimitBridgeStableCofinal {ℓ = ℓ} {ℓW = ℓW} K RS

  Claim : Assumptions → Set
  Claim _ = GRH_Without_Vacuity_Guards RS

  record Pack (A : Assumptions) : Set (lsuc (ℓ ⊔ lsuc ℓW)) where
    field
      claim : Claim A

  mkPack : (A : Assumptions) → Pack A
  mkPack A =
    record
      { claim =
          AccessibleWeilMeetLimitBridgeStableCofinal.GRH_Without_Vacuity_Guards-from-cofinal A
      }
