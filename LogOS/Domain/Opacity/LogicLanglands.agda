{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.LogicLanglands where

open import LogOS.Prelude
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Closure using (ClosureOp)
open import LogOS.Minimal.Con
open import LogOS.Kernel

open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann using (RiemannSpectral)
open import LogOS.Domain.Opacity.NumberTheory.LFunction.ZerosPack using (GRH_Without_Vacuity_Guards)

import LogOS.Theorems.Meta.GRHBridge as GRHB
import LogOS.Theorems.Meta.MathTruth as MT
import LogOS.Theorems.Meta.LimitPublicisation as LP

import LogOS.Domain.Opacity.AccessibleWeilMeetLimitBridgeStableCofinal as Stable
import LogOS.Domain.Opacity.WeilProbeImplication as WPI
import LogOS.Domain.Opacity.TruthSeparation as TruthSep
import LogOS.Domain.Opacity.TruthSeparationForcing as TruthSepF

open TruthSep using (RStoSP; FlowTruthSeparation)

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
    weilProbe  : WPI.WeilProbeImplication RS (Kernel.Code K) W∞
    schedule   : LogicLanglandsSchedule K RS pack

-- | Expose the canonical “Logic Langlands” square that connects:
--   1. finite regulators and their MathTruth pack,
--   2. the Flow projector on the boundary, and
--   3. the Flow-based truth separation (a restriction of forcing).
record LogicLanglandsSquare {ℓ ℓW : Level}
                           {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                           (K : Kernel Sig Q)
                           (RS : RiemannSpectral)
                           (pack : Stable.AccessibleWeilMeetLimitBridgeStableCofinal
                                   {ℓ = ℓ} {ℓW = ℓW} K RS)
                           (Sep : FlowTruthSeparation K RS)
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
    (Sep : FlowTruthSeparation K RS)
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
  ; globalBridge       = TruthSep.flowNucleusBridge K RS Sep
  ; accessiblePath     = Stable.AccessibleWeilMeetLimitBridgeStableCofinal.GRH_Without_Vacuity_Guards-from-cofinal pack
  ; truthSeparationPath = TruthSep.GRH_Without_Vacuity_Guards_from_FlowTruthSeparation K RS Sep
  }

-- Forcing/nucleus variant: replace Flow-local separation with an arbitrary closure operator J.
record LogicLanglandsSquareForcing {ℓ ℓW : Level}
                           {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                           (K : Kernel Sig Q)
                           (RS : RiemannSpectral)
                           (pack : Stable.AccessibleWeilMeetLimitBridgeStableCofinal
                                   {ℓ = ℓ} {ℓW = ℓW} K RS)
                           (J   : ClosureOp (BulkBoundary.bnd (Kernel.BB K)))
                           (Sep : TruthSepF.ProperForcingTruthSeparation K RS J)
  : Set (lsuc (ℓ ⊔ ℓW ⊔ lsuc ℓW)) where
  field
    metadata       : LogicLanglandsMetadata K RS pack
    globalBridge   : GRHB.GlobalNucleusBridge K (RStoSP RS)
    accessiblePath : GRH_Without_Vacuity_Guards RS
    forcingPath    : GRH_Without_Vacuity_Guards RS

logicLanglandsSquareForcing
  : ∀ {ℓ ℓW}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (RS : RiemannSpectral)
    (pack : Stable.AccessibleWeilMeetLimitBridgeStableCofinal
           {ℓ = ℓ} {ℓW = ℓW} K RS)
    (J   : ClosureOp (BulkBoundary.bnd (Kernel.BB K)))
    (Sep : TruthSepF.ProperForcingTruthSeparation K RS J)
  → LogicLanglandsSquareForcing K RS pack J Sep
logicLanglandsSquareForcing K RS pack J Sep = record
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
  ; globalBridge   = TruthSepF.forcingNucleusBridge K RS J (TruthSepF.ProperForcingTruthSeparation.sep Sep)
  ; accessiblePath = Stable.AccessibleWeilMeetLimitBridgeStableCofinal.GRH_Without_Vacuity_Guards-from-cofinal pack
  ; forcingPath    = TruthSepF.GRH_Without_Vacuity_Guards_from_ProperForcingTruthSeparation K RS J Sep
  }
