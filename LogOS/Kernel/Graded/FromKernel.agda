{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Graded.FromKernel where

-- Optional conservativity bridge:
-- lift any ungraded `Kernel` into a `GradedKernel` by using a constant-by-grade flow.
--
-- This shows graded kernels are a conservative interface extension: they do not
-- add logical strength by themselves; they add an additional resource index.

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel
open import LogOS.Kernel.Graded
open import LogOS.Kernel.Graded.ToKernel as ToKernel using (StepIsSat; asKernel)

record TopGrade {ℓ : Level} (Q : QAdapter ℓ) : Set (lsuc ℓ) where
  open QAdapter Q
  field
    top     : Scale
    top-top : ∀ g → _≤s_ g top

-- Build a constant-by-grade GradedClosure from an ordinary GuardedClosure.
-- Saturation is chosen as the designated `top` grade.

gradedClosureFromKernel
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → TopGrade Q
  → GradedClosure Q (BulkBoundary.bnd (Kernel.BB K))
gradedClosureFromKernel {Sig = Sig} {Q = Q} K TG =
  let
    open Kernel K
    open TopGrade TG
    module GT0 = Truth.GuardedTruth Sig Q
    open GT0.GuardedClosure GTruth renaming
      ( Flow      to F
      ; mono      to monoF
      ; infl      to inflF
      ; idemp-lax to idempF
      ; Th*       to Th
      ; Th*-fixed to Th-fixed
      )
    CP = BulkBoundary.bnd BB
  in
  record
    { Flow       = λ _ c → F c
    ; mono       = λ {g} le → monoF le
    ; mono-grade = λ {g} {g'} _ c → ConPoset.refl CP
    ; comp-lax   = λ g g' c → idempF c
    ; sat        = top
    ; sat-top    = top-top
    ; infl-sat   = inflF
    ; idemp-sat  = idempF
    ; Th*        = Th
    ; Th*-fixed  = Th-fixed
    }

fromKernel
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → TopGrade Q
  → GradedKernel Sig Q
fromKernel {Sig = Sig} {Q = Q} K TG =
  let
    open Kernel K
    open TopGrade TG
    G : GradedClosure Q (BulkBoundary.bnd BB)
    G = gradedClosureFromKernel K TG
  in
  record
    { HWorld        = HWorld
    ; BB            = BB
    ; MBulk         = MBulk
    ; MBnd          = MBnd
    ; Holo          = Holo
    ; HTruth        = HTruth
    ; HInv          = HInv
    ; Sat_H_bnd     = Sat_H_bnd
    ; sat-coh       = sat-coh
    ; Fml           = Fml
    ; Strict        = Strict
    ; TransH        = TransH
    ; coh-LH        = coh-LH
    ; GTruth        = G
    ; Code          = Code
    ; encode        = encode
    ; decode        = decode
    ; decode∘encode = decode∘encode
    ; Guard         = Guard
    ; Body          = Body
    ; step-grade    = TopGrade.top TG
    ; guard-decode  = guard-decode
    ; γ*            = γ*
    ; γ*-guard      = γ*-guard
    ; decode-γ*     = decode-γ*
    ; reify         = reify
    ; reify-decode  = reify-decode
    ; Body∂         = Body∂
    ; body-decode   = body-decode
    }

stepIsSat-fromKernel
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q) (TG : TopGrade Q)
  → StepIsSat (fromKernel K TG)
stepIsSat-fromKernel K TG =
  record { step≡sat = refl }

-- Converting back (forget grading at sat) yields the original kernel.
-- This holds propositionally; in most models it is definitional.

asKernel-fromKernel
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q) (TG : TopGrade Q)
  → Kernel Sig Q
asKernel-fromKernel K TG =
  asKernel (fromKernel K TG) (stepIsSat-fromKernel K TG)

-- Note: `asKernel-fromKernel K TG` and `K` have the same *data* fields by
-- construction (BB/World/Code/encode/decode/Guard/Body/Body∂/…); they can differ
-- only in proof fields such as `guard-decode`, since `ToKernel.asKernel` wraps
-- the graded `guard-decode` with a transport along `step≡sat`.
