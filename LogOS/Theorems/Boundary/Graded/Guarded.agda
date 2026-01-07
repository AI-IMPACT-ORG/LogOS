{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Boundary.Graded.Guarded where

-- Guarded code theorems (graded kernel): decode-level preservation of γ* and
-- guard naturality under graded kernel homomorphisms.

open import LogOS.Prelude
open import Data.Product using (_×_; _,_; fst; snd)

open import LogOS.Kernel.Graded
open import LogOS.Kernel.Graded.Hom
open import LogOS.Algebra.ConAlg
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter

-- If a graded kernel hom preserves Flow (via GradedKernelHomFlow), then the mapped
-- guarded fixed-point in the target decodes below Th* (lax preservation).

decode-mapCode-γ*≤Th*
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K₁ K₂ : GradedKernel Sig Q)
    (h  : GradedKernelHom K₁ K₂)
    (ht : GradedKernelHomFlow K₁ K₂ h)
  → ConPoset._⊑_ (BulkBoundary.bnd (GradedKernel.BB K₂))
                 (GradedKernel.decode K₂ (GradedKernelHom.mapCode h (GradedKernel.γ* K₁)))
                 (GradedClosure.Th* (GradedKernel.GTruth K₂))
decode-mapCode-γ*≤Th* {Sig = Sig} {Q = Q} K₁ K₂ h ht =
  let open GradedKernel K₁ renaming (BB to BB₁; GTruth to G₁)
      open GradedKernel K₂ renaming (BB to BB₂; GTruth to G₂)
      module GT0 = Truth.GuardedCore
      open GradedKernelHom h
      open GradedKernelHomFlow ht
      open GT0.GradedFlowHom flow-hom using (preserves-Th)
      map∂ = ConAlgHom≡.map∂ (GradedKernelHom.con-hom h)
      eq₁ : GradedKernel.decode K₂ (GradedKernelHom.mapCode h (GradedKernel.γ* K₁))
            ≡ map∂ (GradedKernel.decode K₁ (GradedKernel.γ* K₁))
      eq₁ = GradedKernelHom.map-decode h (GradedKernel.γ* K₁)
      eq₂ : GradedKernel.decode K₁ (GradedKernel.γ* K₁) ≡ GradedClosure.Th* G₁
      eq₂ = GradedKernel.decode-γ* K₁
  in subst (λ x → ConPoset._⊑_ (BulkBoundary.bnd BB₂) x (GradedClosure.Th* G₂))
           (sym (trans eq₁ (cong map∂ eq₂)))
           preserves-Th
