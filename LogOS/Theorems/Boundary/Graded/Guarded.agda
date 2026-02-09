{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Boundary.Graded.Guarded where

-- Guarded code theorems (graded kernel): decode-level preservation of γ* and
-- guard naturality under graded kernel homomorphisms.

open import LogOS.Prelude
open import LogOS.Prelude using (_×_; _,_; fst; snd)

open import LogOS.Kernel.Graded
open import LogOS.Kernel.Graded.Hom
open import LogOS.Minimal.ConAlg
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
import LogOS.Theorems.Boundary.MuFusion as MuFusion

-- If a graded kernel hom transports `Th*` (via `GradedKernelHomFlowStable`), then
-- the mapped guarded fixed-point in the target decodes below Th* (lax preservation).

decode-mapCode-γ*≤Th*
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K₁ K₂ : GradedKernel Sig Q)
    (h  : GradedKernelHom K₁ K₂)
    (ht : GradedKernelHomFlowStable K₁ K₂ h)
  → ConPreorder._⊑_ (BulkBoundary.bnd (GradedKernel.BB K₂))
                 (GradedKernel.decode K₂ (GradedKernelHom.mapCode h (GradedKernel.γ* K₁)))
                 (GradedClosure.Th* (GradedKernel.GTruth K₂))
decode-mapCode-γ*≤Th* {Sig = Sig} {Q = Q} K₁ K₂ h ht =
  let open GradedKernel K₁ renaming (BB to BB₁; GTruth to G₁)
      open GradedKernel K₂ renaming (BB to BB₂; GTruth to G₂)
      open GradedKernelHom h
      open GradedKernelHomFlowStable ht
      map∂ = ConAlgHom≡.map∂ (GradedKernelHom.con-hom h)
      eq₁ : GradedKernel.decode K₂ (GradedKernelHom.mapCode h (GradedKernel.γ* K₁))
            ≡ map∂ (GradedKernel.decode K₁ (GradedKernel.γ* K₁))
      eq₁ = GradedKernelHom.map-decode h (GradedKernel.γ* K₁)
      eq₂ : GradedKernel.decode K₁ (GradedKernel.γ* K₁) ≡ GradedClosure.Th* G₁
      eq₂ = GradedKernel.decode-γ* K₁
  in subst (λ x → ConPreorder._⊑_ (BulkBoundary.bnd BB₂) x (GradedClosure.Th* G₂))
           (sym (trans eq₁ (cong map∂ eq₂)))
           preserves-Th

-- Variant: derive `GradedKernelHomFlowStable` from step preservation using μ-fusion
-- at the saturation grade.

module ForHom
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K₁ K₂ : GradedKernel Sig Q)
  (h : GradedKernelHom K₁ K₂)
  where
  private
    module GT = Truth.GuardedCore {ℓ = ℓ}

    CP₁ : ConPreorder ℓ
    CP₁ = BulkBoundary.bnd (GradedKernel.BB K₁)

    CP₂ : ConPreorder ℓ
    CP₂ = BulkBoundary.bnd (GradedKernel.BB K₂)

    GC₁sat : GT.GuardedClosure CP₁
    GC₁sat = GT.forgetGradedClosure (GradedKernel.GTruth K₁)

    GC₂sat : GT.GuardedClosure CP₂
    GC₂sat = GT.forgetGradedClosure (GradedKernel.GTruth K₂)

  decode-mapCode-γ*≤Th*-fromFlow
    : (hf : GradedKernelHomFlow K₁ K₂ h)
    → MuFusion.GradedKernel.GradedKernelHomStabilisationAssumptions {K₁ = K₁} {K₂ = K₂} {h = h}
    → ConPreorder._⊑_ CP₂
        (GradedKernel.decode K₂ (GradedKernelHom.mapCode h (GradedKernel.γ* K₁)))
        (GradedClosure.Th* (GradedKernel.GTruth K₂))
  decode-mapCode-γ*≤Th*-fromFlow hf A =
    decode-mapCode-γ*≤Th* K₁ K₂ h
      (MuFusion.GradedKernel.gradedKernelHomFlowStable-from hf A)
