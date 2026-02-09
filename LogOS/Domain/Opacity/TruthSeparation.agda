{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
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
open import LogOS.Minimal.Adjunction using (LaxMonoidalAdjunction)
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel

open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann using (RiemannSpectral)
open import LogOS.Domain.Opacity.SpectralPack public
open import LogOS.Domain.Opacity.TruthSeparationForcing public

import LogOS.Theorems.Meta.GRHBridge as GRHB
import LogOS.Theorems.CategoryTheory.AdjunctionMonads as AdjunctionMonads

-- Flow as a closure operator on the boundary preorder.
FlowClosureOp
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → ClosureOp (BulkBoundary.bnd (Kernel.BB K))
FlowClosureOp {ℓ = ℓ} K =
  let module GC = Truth.GuardedCore {ℓ = ℓ} in
  GC.closureOfGuardedClosure (GTruth K)

-- Optional strengthening: use the boundary closure induced by the bulk↔boundary
-- adjunction `ext ⊣ bnd`, i.e. `T = bnd ∘ ext`, as a forcing nucleus.
--
-- This requires monotonicity for `ext` and `bnd` (not part of the minimal kernel
-- shape). The closure itself is still only *lax* (idempotence up to ≤).

AdjunctionClosureOp
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (ext-mono : MonoMap
      (BulkBoundary.bnd (Kernel.BB K))
      (BulkBoundary.bulk (Kernel.BB K))
      (LaxMonoidalAdjunction.ext (Kernel.Holo K)))
    (bnd-mono : MonoMap
      (BulkBoundary.bulk (Kernel.BB K))
      (BulkBoundary.bnd (Kernel.BB K))
      (LaxMonoidalAdjunction.bnd (Kernel.Holo K)))
  → ClosureOp (BulkBoundary.bnd (Kernel.BB K))
AdjunctionClosureOp K ext-mono bnd-mono =
  let
    module D = AdjunctionMonads.Derived
      (LaxMonoidalAdjunction.core (Kernel.Holo K))
      ext-mono
      bnd-mono
  in
  D.T-closureOp

-- Flow-based separation is a forcing separation with J = Flow.
FlowTruthSeparation
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (RS : RiemannSpectral)
  → Set (lsuc (ℓ ⊔ lzero))
FlowTruthSeparation K RS = ForcingTruthSeparation K RS (FlowClosureOp K)

AdjunctionTruthSeparation
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (RS : RiemannSpectral)
    (ext-mono : MonoMap
      (BulkBoundary.bnd (Kernel.BB K))
      (BulkBoundary.bulk (Kernel.BB K))
      (LaxMonoidalAdjunction.ext (Kernel.Holo K)))
    (bnd-mono : MonoMap
      (BulkBoundary.bulk (Kernel.BB K))
      (BulkBoundary.bnd (Kernel.BB K))
      (LaxMonoidalAdjunction.bnd (Kernel.Holo K)))
  → Set (lsuc (ℓ ⊔ lzero))
AdjunctionTruthSeparation K RS ext-mono bnd-mono =
  ForcingTruthSeparation K RS (AdjunctionClosureOp K ext-mono bnd-mono)

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
