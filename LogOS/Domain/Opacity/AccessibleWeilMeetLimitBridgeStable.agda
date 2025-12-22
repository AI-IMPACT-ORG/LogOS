{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.AccessibleWeilMeetLimitBridgeStable where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

import LogOS.Theorems.Meta.CommunicableTruth as Comm
import LogOS.Theorems.Meta.MathTruth as MT
import LogOS.Theorems.Meta.LimitPublicisation as LP

open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann using (RiemannSpectral)
open import LogOS.Domain.Opacity.NumberTheory.LFunction.ZerosPack using (GRH_Without_Vacuity_Guards)

import LogOS.Domain.Opacity.AccessibleWeilMeetLimitBridge as AWLM

-- Variant of the meet-limit bridge where the per-regulator “completeness” premise
-- is reduced to a plain truth fact `Wᵢ i (probe s)`, provided each regulator
-- predicate is itself Flow-stable and decode-extensional.
--
-- This matches the informal axiom “stable properties are observable”: if a
-- regulator predicate Wᵢ is already stable under FlowCode (and extensional),
-- then Wᵢ implies its own publicisation `Pr Wᵢ` by `LP.TruthK→Pr`.

record AccessibleWeilMeetLimitBridgeStable {ℓ ℓW : Level}
                                           {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                                           (K  : Kernel Sig Q)
                                           (RS : RiemannSpectral)
                                           : Set (lsuc (ℓ ⊔ lsuc ℓW)) where
  open RiemannSpectral RS

  field
    -- Use MathTruth with communicability level specialised to ℓW so we can
    -- derive `Pr Wᵢ` directly from `Wᵢ`.
    Reg : MT.MathTruth {ℓ} {ℓW} {ℓW} K

  open MT.MathTruth Reg public
    renaming (Idx to Idx; Truthᵢ to Wᵢ; Truth∞ to W∞)

  field
    -- Weil direction at the limit.
    WProbe : AWLM.WeilProbeImplication RS (Kernel.Code K) W∞

    -- Each regulator predicate is stable/extensional (so it is self-observable).
    Wᵢ-ext : ∀ i → Comm.DecodeExtensional′ K (Wᵢ i)
    Wᵢ-stable : ∀ i γ → (Wᵢ i γ) ↔ (Wᵢ i (FlowCode K γ))

    -- Plain finite evidence: at every regulator, the probe test satisfies Wᵢ.
    holdsᵢ : ∀ i s → NontrivialZero s → Wᵢ i (AWLM.WeilProbeImplication.probe WProbe s)

  -- Derived regulator-wise observability from stability/extensionality.
  completeᵢ
    : ∀ i s → NontrivialZero s
      → Comm.Pr {ℓC = ℓW} K (Wᵢ i) (AWLM.WeilProbeImplication.probe WProbe s)
  completeᵢ i s nz =
    LP.TruthK→Pr K (Wᵢ i) (Wᵢ-ext i) (Wᵢ-stable i) (holdsᵢ i s nz)

  -- Package into the original meet-limit bridge (at ℓC = ℓW) and conclude GRH.
  Bridge : AWLM.AccessibleWeilMeetLimitBridge {ℓ = ℓ} {ℓW = ℓW} {ℓC = ℓW} K RS
  Bridge = record
    { Reg       = Reg
    ; WProbe    = WProbe
    ; completeᵢ = completeᵢ
    }

  GRH_Without_Vacuity_Guards-from-stable-bridge : GRH_Without_Vacuity_Guards RS
  GRH_Without_Vacuity_Guards-from-stable-bridge =
    AWLM.GRH_Without_Vacuity_Guards_from_AccessibleWeilMeetLimitBridge {ℓC = ℓW} K RS Bridge

  -- Cofinal scheduling (“regulator independence”): the meet-limit truth predicate
  -- is unchanged up to pointwise logical equivalence under a cofinal reindexing,
  -- assuming the regulator family is antitone in the index order.

  W∞-cofinal
    : ∀ {B : Set}
      (PIdx : LP.Preorder Idx)
      (u    : B → Idx)
      (cof  : LP.Cofinal PIdx u)
      (antiMono : ∀ {i j} → LP.Preorder._≤_ PIdx i j → ∀ {γ} → Wᵢ j γ → Wᵢ i γ)
    → ∀ {γ} → W∞ γ ↔ (∀ b → Wᵢ (u b) γ)
  W∞-cofinal PIdx u cof antiMono {γ} =
    Truth∞-cofinal PIdx u cof antiMono {γ = γ}

  Observable-cofinal′
    : ∀ {B : Set}
      (PIdx : LP.Preorder Idx)
      (u    : B → Idx)
      (cof  : LP.Cofinal PIdx u)
      (antiMono : ∀ {i j} → LP.Preorder._≤_ PIdx i j → ∀ {γ} → Wᵢ j γ → Wᵢ i γ)
    → ∀ {γ} → Observable γ ↔ Comm.Pr {ℓC = ℓW} K (λ γ → ∀ b → Wᵢ (u b) γ) γ
  Observable-cofinal′ PIdx u cof antiMono {γ} =
    MT.MathTruth.Observable-cofinal Reg PIdx u cof antiMono {γ = γ}

-- --------------------------------------------------------------------------
-- Standard pack skeleton (uniform API).

module QuartetMeetLimitStable
  {ℓ ℓW}
  {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K  : Kernel Sig Q)
  (RS : RiemannSpectral)
  where

  Assumptions : Set (lsuc (ℓ ⊔ lsuc ℓW))
  Assumptions = AccessibleWeilMeetLimitBridgeStable {ℓ = ℓ} {ℓW = ℓW} K RS

  Claim : Assumptions → Set
  Claim _ = GRH_Without_Vacuity_Guards RS

  record Pack (A : Assumptions) : Set (lsuc (ℓ ⊔ lsuc ℓW)) where
    field
      claim : Claim A

  mkPack : (A : Assumptions) → Pack A
  mkPack A =
    record
      { claim =
          AccessibleWeilMeetLimitBridgeStable.GRH_Without_Vacuity_Guards-from-stable-bridge A
      }
