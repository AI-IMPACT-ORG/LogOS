{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.PNTBridge where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Closure using (ClosureOp; cl)
open import LogOS.Kernel

open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann using (RiemannSpectral)
open import LogOS.Domain.Opacity.TruthSeparation as TruthSep
import LogOS.Domain.Opacity.TruthSeparationForcing as TruthSepF

-- Forcing-style variant: replace Flow with a chosen closure operator J.

record PNTFromForcingTruthSeparation {ℓ}
                                    {Sig : LogOSSignature ℓ}
                                    {Q   : QAdapter ℓ}
                                    (K   : Kernel Sig Q)
                                    (RS  : RiemannSpectral)
                                    (J   : ClosureOp (BulkBoundary.bnd (Kernel.BB K)))
                                    (Sep : TruthSepF.ForcingTruthSeparation K RS J)
                                    : Set (lsuc ℓ) where
  open Kernel K
  open TruthSepF.ForcingTruthSeparation Sep

  field
    PNT : Set ℓ
    pntC : ConPreorder.Con CP
    pnt-J-closed : ConPreorder._⊑_ CP (cl J pntC) pntC
    JClosed→PNT : ConPreorder._⊑_ CP (cl J pntC) pntC → PNT

  PNT-from-separation : PNT
  PNT-from-separation = JClosed→PNT pnt-J-closed

  GRH_Without_Vacuity_Guards
    : ∀ s → RiemannSpectral.NontrivialZero RS s → RiemannSpectral.OnLine RS s
  GRH_Without_Vacuity_Guards =
    TruthSepF.GRH_Without_Vacuity_Guards_from_ForcingTruthSeparation K RS J Sep

-- Flow-based PNT is a restriction of the forcing-style interface.
PNTFromFlowTruthSeparation
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K   : Kernel Sig Q)
    (RS  : RiemannSpectral)
    (Sep : TruthSep.FlowTruthSeparation K RS)
  → Set (lsuc ℓ)
PNTFromFlowTruthSeparation K RS Sep =
  PNTFromForcingTruthSeparation K RS (TruthSep.FlowClosureOp K) Sep
