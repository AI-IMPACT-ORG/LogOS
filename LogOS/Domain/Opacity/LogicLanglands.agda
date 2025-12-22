{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.LogicLanglands where

open import LogOS.Prelude
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann using (RiemannSpectral)
open import LogOS.Domain.Opacity.NumberTheory.LFunction.ZerosPack using (GRH_Without_Vacuity_Guards)

import LogOS.Theorems.Meta.GRHBridge as GRHB
import LogOS.Theorems.Meta.MathTruth as MT
import LogOS.Theorems.Meta.LimitPublicisation as LP

import LogOS.Domain.Opacity.AccessibleWeilMeetLimitBridgeStableCofinal as Stable
import LogOS.Domain.Opacity.AccessibleWeilMeetLimitBridge as AWLM
import LogOS.Domain.Opacity.TruthSeparation as TruthSep

open TruthSep using (RStoSP; GlobalTruthSeparation)

-- | Store the cofinal schedule data (index order, schedule map, anti-monotonicity).
record LogicLanglandsSchedule {ℓ ℓW : Level}
                             {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                             (K : Kernel Sig Q)
                             (RS : RiemannSpectral)
                             (pack : Stable.AccessibleWeilMeetLimitBridgeStableCofinal
                                    {ℓ = ℓ} {ℓW = ℓW} K RS)
  : Set (lsuc (ℓ ⊔ ℓW)) where
  open Stable.AccessibleWeilMeetLimitBridgeStableCofinal pack public
  field
    idxOrder      : LP.Preorder Idx
    schedule      : B → Idx
    cofinality    : LP.Cofinal idxOrder schedule
    antiMonoProof : ∀ {i j} → LP.Preorder._≤_ idxOrder i j
                  → ∀ {γ} → Wᵢ j γ → Wᵢ i γ

-- | Bundle the regulator pack, Weil probe, and schedule into a single metadata record.
record LogicLanglandsMetadata {ℓ ℓW : Level}
                             {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                             (K : Kernel Sig Q)
                             (RS : RiemannSpectral)
                             (pack : Stable.AccessibleWeilMeetLimitBridgeStableCofinal
                                    {ℓ = ℓ} {ℓW = ℓW} K RS)
  : Set (lsuc (ℓ ⊔ ℓW ⊔ lsuc ℓW)) where
  open Stable.AccessibleWeilMeetLimitBridgeStableCofinal pack public
  field
    regulators : MT.MathTruth {ℓ = ℓ} {ℓT = ℓW} {ℓC = ℓW} K
    weilProbe  : AWLM.WeilProbeImplication RS (Kernel.Code K) W∞
    schedule   : LogicLanglandsSchedule K RS pack

-- | Expose the canonical “Logic Langlands” square that connects:
--   1. finite regulators and their MathTruth pack,
--   2. the Flow projector on the boundary, and
--   3. the global/local truth bridge that sends zeros on the line.
record LogicLanglandsSquare {ℓ ℓW : Level}
                           {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                           (K : Kernel Sig Q)
                           (RS : RiemannSpectral)
                           (pack : Stable.AccessibleWeilMeetLimitBridgeStableCofinal
                                   {ℓ = ℓ} {ℓW = ℓW} K RS)
                           (Sep : GlobalTruthSeparation K RS)
  : Set (lsuc (ℓ ⊔ ℓW ⊔ lsuc ℓW)) where
  field
    metadata            : LogicLanglandsMetadata K RS pack
    globalBridge        : GRHB.GlobalNucleusBridge K (RStoSP RS)
    accessiblePath      : GRH_Without_Vacuity_Guards RS
    truthSeparationPath : GRH_Without_Vacuity_Guards RS

-- | Build the square from the happy-path bridge and a TruthSeparation witness.
logicLanglandsSquare
  : ∀ {ℓ ℓW}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (RS : RiemannSpectral)
    (pack : Stable.AccessibleWeilMeetLimitBridgeStableCofinal
           {ℓ = ℓ} {ℓW = ℓW} K RS)
    (Sep : GlobalTruthSeparation K RS)
  → LogicLanglandsSquare K RS pack Sep
logicLanglandsSquare K RS pack Sep = record
  { metadata = record
      { regulators = Stable.AccessibleWeilMeetLimitBridgeStableCofinal.Reg pack
      ; weilProbe  = Stable.AccessibleWeilMeetLimitBridgeStableCofinal.WProbe pack
      ; schedule   =
          record
            { idxOrder      = Stable.AccessibleWeilMeetLimitBridgeStableCofinal.PIdx pack
            ; schedule      = Stable.AccessibleWeilMeetLimitBridgeStableCofinal.u pack
            ; cofinality    = Stable.AccessibleWeilMeetLimitBridgeStableCofinal.cof pack
            ; antiMonoProof = Stable.AccessibleWeilMeetLimitBridgeStableCofinal.antiMono pack
            }
      }
  ; globalBridge       = TruthSep.globalNucleusBridge K RS Sep
  ; accessiblePath     = Stable.AccessibleWeilMeetLimitBridgeStableCofinal.GRH_Without_Vacuity_Guards-from-cofinal pack
  ; truthSeparationPath = TruthSep.GRH_Without_Vacuity_Guards_from_GlobalTruthSeparation K RS Sep
  }
