{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.TruthSeparationForcing where

open import LogOS.Prelude
open import Data.Product using (_×_; _,_; proj₁)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Closure using (ClosureOp; cl; infl; idemp-lax)
open import LogOS.Kernel
import LogOS.Kernel.LogicKernel.FromKernel as LK
import LogOS.Kernel.LogicKernel.EndoRelative as EndoRel

open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann using (RiemannSpectral)
open import LogOS.Domain.Opacity.SpectralPack using (RStoSP)

import LogOS.Theorems.Meta.GRHBridge as GRHB
import LogOS.Theorems.Projective as Proj

-- A ClosureOp is a nucleus/forcing modality; lift it to a Projector.
projectorFromClosureOp
  : ∀ {ℓ} {CP : ConPoset ℓ} → ClosureOp CP → Proj.Projector CP
projectorFromClosureOp C = record
  { P         = cl C
  ; infl      = infl C
  ; idemp-lax = idemp-lax C
  }

-- Forcing-style truth separation: close with an arbitrary nucleus J rather than Flow.
record ForcingTruthSeparation {ℓ}
                              {Sig : LogOSSignature ℓ}
                              {Q   : QAdapter ℓ}
                              (K   : Kernel Sig Q)
                              (RS  : RiemannSpectral)
                              (J   : ClosureOp (BulkBoundary.bnd (Kernel.BB K)))
                              : Set (lsuc (ℓ ⊔ lzero)) where
  open Kernel K
  open RiemannSpectral RS
  CP = BulkBoundary.bnd BB

  field
    c : Spectral → ConPoset.Con CP

    zero→JClosed
      : ∀ s → NontrivialZero s → ConPoset._⊑_ CP (cl J (c s)) (c s)

    JClosed→OnLine
      : ∀ s → ConPoset._⊑_ CP (cl J (c s)) (c s) → OnLine s

forcingNucleusBridge
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K   : Kernel Sig Q)
    (RS  : RiemannSpectral)
    (J   : ClosureOp (BulkBoundary.bnd (Kernel.BB K)))
    (Sep : ForcingTruthSeparation K RS J)
  → GRHB.GlobalNucleusBridge K (RStoSP RS)
forcingNucleusBridge K RS J Sep =
  let open ForcingTruthSeparation Sep
  in record
       { Pr = projectorFromClosureOp J
       ; c  = c
       ; zero→PFixed = λ s nz → zero→JClosed s nz , infl J (c s)
       ; PFixed→OnLine = λ s fixed → JClosed→OnLine s (fst fixed)
       }

GRH_Without_Vacuity_Guards_from_ForcingTruthSeparation
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K   : Kernel Sig Q)
    (RS  : RiemannSpectral)
    (J   : ClosureOp (BulkBoundary.bnd (Kernel.BB K)))
    (Sep : ForcingTruthSeparation K RS J)
  → ∀ s → RiemannSpectral.NontrivialZero RS s → RiemannSpectral.OnLine RS s
GRH_Without_Vacuity_Guards_from_ForcingTruthSeparation K RS J Sep =
  GRHB.GRH_Without_Vacuity_Guards_via_GlobalNucleus K (RStoSP RS)
    (forcingNucleusBridge K RS J Sep)

-- Closure-step calculus relative to a forcing nucleus J (LogicKernel-level).
module ForcingSteps
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K   : Kernel Sig Q)
  (J   : ClosureOp (BulkBoundary.bnd (Kernel.BB K)))
  where

  module F = EndoRel.FromClosureOp (LK.asLogicKernel K) J
  open F.Rel public using
    ( ClosureStep; mkClosureStep; J-closeStep; _∘Step_; _thenStep_ )
