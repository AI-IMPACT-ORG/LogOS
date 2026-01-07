{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.TruthSeparation where

-- Flow-based truth separation is now a specialization of the forcing/nucleus
-- interface. The forcing version is the primary abstraction.

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Closure using (ClosureOp)
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel

open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann using (RiemannSpectral)
open import LogOS.Domain.Opacity.SpectralPack public
open import LogOS.Domain.Opacity.TruthSeparationForcing public

import LogOS.Theorems.Meta.GRHBridge as GRHB

-- Flow as a closure operator on the boundary poset.
FlowClosureOp
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → ClosureOp (BulkBoundary.bnd (Kernel.BB K))
FlowClosureOp K =
  Truth.GuardedCore.closureOfGuardedClosure (Kernel.GTruth K)

-- Flow-based separation is a forcing separation with J = Flow.
FlowTruthSeparation
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (RS : RiemannSpectral)
  → Set (lsuc (ℓ ⊔ lzero))
FlowTruthSeparation K RS = ForcingTruthSeparation K RS (FlowClosureOp K)

flowNucleusBridge
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K   : Kernel Sig Q)
    (RS  : RiemannSpectral)
    (Sep : FlowTruthSeparation K RS)
  → GRHB.GlobalNucleusBridge K (RStoSP RS)
flowNucleusBridge K RS Sep =
  forcingNucleusBridge K RS (FlowClosureOp K) Sep

GRH_Without_Vacuity_Guards_from_FlowTruthSeparation
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K   : Kernel Sig Q)
    (RS  : RiemannSpectral)
    (Sep : FlowTruthSeparation K RS)
  → ∀ s → RiemannSpectral.NontrivialZero RS s → RiemannSpectral.OnLine RS s
GRH_Without_Vacuity_Guards_from_FlowTruthSeparation K RS Sep =
  GRH_Without_Vacuity_Guards_from_ForcingTruthSeparation K RS (FlowClosureOp K) Sep

module FlowSteps
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K   : Kernel Sig Q)
  where

  open ForcingSteps K (FlowClosureOp K) public
