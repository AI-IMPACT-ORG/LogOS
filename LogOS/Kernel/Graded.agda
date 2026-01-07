{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Graded where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel.Core as Core

open Truth.GuardedCore public using
  ( GradedClosure
  ; GradeHom
  ; GradedFlowHom
  ; GradedFlowHomWithGrade
  ; forgetGradedClosure
  )

-- Graded kernel: same shared shape as `Kernel`, but guarded flow is grade-indexed.
record GradedKernel {ℓ : Level} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
  : Set (lsuc (lsuc ℓ)) where
  field
    shape : Core.KernelShape Sig Q
  open Core.KernelShape shape public

  field
    -- G-tier: graded guarded closure on boundary constraints
    GTruth     : GradedClosure Q (BulkBoundary.bnd (Core.KernelShape.BB shape))
    step-grade : QAdapter.Scale Q

    -- Kernel coherence: `Guard` internalises the one-step (step-grade) flow at decode level.
    guard-decode
      : ∀ γ
      → Core.KernelShape.decode shape (Core.KernelShape.Guard shape γ)
        ≡ GradedClosure.Flow GTruth step-grade (Core.KernelShape.decode shape γ)

    -- Distinguished code witness decodes to the saturation-grade fixed point.
    decode-γ* : Core.KernelShape.decode shape (Core.KernelShape.γ* shape) ≡ GradedClosure.Th* GTruth

-- Derived code-level Flow (Guard ∘ Body).
FlowCode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q) → GradedKernel.Code K → GradedKernel.Code K
FlowCode K = Core.FlowCodeShape (GradedKernel.shape K)

decode-FlowCode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q) (γ : GradedKernel.Code K)
  → GradedKernel.decode K (FlowCode K γ)
    ≡ GradedClosure.Flow (GradedKernel.GTruth K) (GradedKernel.step-grade K)
        (GradedKernel.Body∂ K (GradedKernel.decode K γ))
decode-FlowCode {Sig = Sig} {Q = Q} K γ =
  trans (GradedKernel.guard-decode K (GradedKernel.Body K γ))
        (cong (GradedClosure.Flow (GradedKernel.GTruth K) (GradedKernel.step-grade K))
              (GradedKernel.body-decode K γ))

-- Step-grade vs saturation-grade friction reducers.
--
-- In a graded kernel, `Guard` decodes to a one-step `Flow step-grade`, while the
-- distinguished fixed point `Th*` lives at the saturation grade. The following
-- derived lemmas make the grade shift explicit and help avoid accidental
-- rewrites of step-grade facts as saturation facts.

-- Step-grade is always ≤ saturation grade (derived from `sat-top`).
step≤sat
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → QAdapter._≤s_ Q (GradedKernel.step-grade K) (GradedClosure.sat (GradedKernel.GTruth K))
step≤sat K = GradedClosure.sat-top (GradedKernel.GTruth K) (GradedKernel.step-grade K)

guard-decode≤sat
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q) (γ : GradedKernel.Code K)
  → ConPoset._⊑_ (BulkBoundary.bnd (GradedKernel.BB K))
      (GradedKernel.decode K (GradedKernel.Guard K γ))
      (GradedClosure.Flow (GradedKernel.GTruth K) (GradedClosure.sat (GradedKernel.GTruth K))
        (GradedKernel.decode K γ))
guard-decode≤sat K γ =
  let open GradedKernel K
      CP = BulkBoundary.bnd (GradedKernel.BB K)
      le = GradedClosure.mono-grade GTruth (step≤sat K) (GradedKernel.decode K γ)
  in subst (λ x → ConPoset._⊑_ CP x (GradedClosure.Flow GTruth (GradedClosure.sat GTruth) (GradedKernel.decode K γ)))
           (sym (guard-decode γ))
           le

decode-FlowCode≤sat
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q) (γ : GradedKernel.Code K)
  → ConPoset._⊑_ (BulkBoundary.bnd (GradedKernel.BB K))
      (GradedKernel.decode K (FlowCode K γ))
      (GradedClosure.Flow (GradedKernel.GTruth K) (GradedClosure.sat (GradedKernel.GTruth K))
        (GradedKernel.Body∂ K (GradedKernel.decode K γ)))
decode-FlowCode≤sat K γ =
  let open GradedKernel K
      CP = BulkBoundary.bnd (GradedKernel.BB K)
      le = GradedClosure.mono-grade GTruth (step≤sat K) (GradedKernel.Body∂ K (GradedKernel.decode K γ))
  in subst (λ x → ConPoset._⊑_ CP x (GradedClosure.Flow GTruth (GradedClosure.sat GTruth) (GradedKernel.Body∂ K (GradedKernel.decode K γ))))
           (sym (decode-FlowCode K γ))
           le
