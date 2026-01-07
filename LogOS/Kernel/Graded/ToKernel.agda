{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
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
    { shape = GradedKernel.shape K
    ; GTruth = forgetGradedClosure (GradedKernel.GTruth K)
    ; guard-decode = guard-decode-sat
    ; decode-γ* = GradedKernel.decode-γ* K
    }
  where
  open StepIsSat stepSat using (step≡sat)
  open GradedKernel K

  guard-decode-sat
    : ∀ γ
    → decode (Guard γ)
      ≡ Truth.GuardedCore.GuardedClosure.Flow
          (forgetGradedClosure (GradedKernel.GTruth K))
          (decode γ)
  guard-decode-sat γ =
    trans (guard-decode γ)
      (cong (λ g → GradedClosure.Flow GTruth g (decode γ)) step≡sat)
