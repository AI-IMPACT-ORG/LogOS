{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Graded.ToKernel where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel
open import LogOS.Kernel.Graded

-- When the code-level guard grade coincides with the saturation grade, a graded
-- kernel can be viewed as an ordinary kernel by forgetting grading at `sat`.

record StepIsSat {ℓ : Level}
                 {Sig : LogOSSignature ℓ}
                 {Q   : QAdapter ℓ}
                 (K   : GradedKernel Sig Q)
                 : Set (lsuc ℓ) where
  field
    step≡sat : GradedKernel.step-grade K ≡ GradedClosure.sat (GradedKernel.GTruth K)

asKernel
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → StepIsSat K
  → Kernel Sig Q
asKernel {Sig = Sig} {Q = Q} K stepSat =
  record
    { HWorld        = GradedKernel.HWorld K
    ; BB            = GradedKernel.BB K
    ; MBulk         = GradedKernel.MBulk K
    ; MBnd          = GradedKernel.MBnd K
    ; Holo          = GradedKernel.Holo K
    ; HTruth        = GradedKernel.HTruth K
    ; HInv          = GradedKernel.HInv K
    ; Sat_H_bnd     = GradedKernel.Sat_H_bnd K
    ; sat-coh       = GradedKernel.sat-coh K
    ; Fml           = GradedKernel.Fml K
    ; Strict        = GradedKernel.Strict K
    ; TransH        = GradedKernel.TransH K
    ; coh-LH        = GradedKernel.coh-LH K
    ; GTruth        = forgetGradedClosure (GradedKernel.GTruth K)
    ; Code          = GradedKernel.Code K
    ; encode        = GradedKernel.encode K
    ; decode        = GradedKernel.decode K
    ; decode∘encode = GradedKernel.decode∘encode K
    ; Guard         = GradedKernel.Guard K
    ; Body          = GradedKernel.Body K
    ; guard-decode  = guard-decode-sat
    ; γ*            = GradedKernel.γ* K
    ; γ*-guard      = GradedKernel.γ*-guard K
    ; decode-γ*     = GradedKernel.decode-γ* K
    ; reify         = GradedKernel.reify K
    ; reify-decode  = GradedKernel.reify-decode K
    ; Body∂         = GradedKernel.Body∂ K
    ; body-decode   = GradedKernel.body-decode K
    }
  where
  open StepIsSat stepSat using (step≡sat)
  open GradedKernel K

  guard-decode-sat : ∀ γ → decode (Guard γ) ≡ GradedClosure.Flow GTruth (GradedClosure.sat GTruth) (decode γ)
  guard-decode-sat γ =
    trans (guard-decode γ)
      (cong (λ g → GradedClosure.Flow GTruth g (decode γ)) step≡sat)

