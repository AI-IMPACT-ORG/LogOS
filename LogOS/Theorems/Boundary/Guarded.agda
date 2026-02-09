{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Boundary.Guarded where

-- Guarded code theorems: decode-level preservation of γ* and guard naturality
-- under Kernel homomorphisms. Proven from Kernel fields (GuardedClosure and
-- KernelHomFlowStable) without additional postulates.

open import LogOS.Prelude
open import LogOS.Prelude using (_×_; _,_; fst; snd)

open import LogOS.Kernel
open import LogOS.Kernel.Hom
open import LogOS.Kernel.Endo
open import LogOS.Minimal.ConAlg
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
import LogOS.Theorems.Boundary.MuFusion as MuFusion

-- If a Kernel hom preserves Flow (via KernelHomFlow), then the mapped
-- guarded fixed-point in the target decodes below Th* (lax preservation).

decode-mapCode-γ*≤Th*
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K₁ K₂ : Kernel Sig Q)
    (h  : KernelHom K₁ K₂)
    (ht : KernelHomFlowStable K₁ K₂ h)
  → ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K₂))
                 (Kernel.decode K₂ (KernelHom.mapCode h (Kernel.γ* K₁)))
                 (Th⋆K K₂)
decode-mapCode-γ*≤Th* {Sig = Sig} {Q = Q} K₁ K₂ h ht =
  let
    BB₁ = Kernel.BB K₁
    BB₂ = Kernel.BB K₂

    G₁ = GTruth K₁
    G₂ = GTruth K₂

    module GT0 = Truth.GuardedTruth Sig Q
    open KernelHom h
    open KernelHomFlowStable ht
    open GT0.GuardedClosure G₁ renaming (Th* to Th₁)
    open GT0.GuardedClosure G₂ renaming (Th* to Th₂)

    map∂ = ConAlgHom≡.map∂ (KernelHom.con-hom h)

    eq₁ : Kernel.decode K₂ (KernelHom.mapCode h (Kernel.γ* K₁)) ≡ map∂ (Kernel.decode K₁ (Kernel.γ* K₁))
    eq₁ = KernelHom.map-decode h (Kernel.γ* K₁)

    eq₂ : Kernel.decode K₁ (Kernel.γ* K₁) ≡ Th₁
    eq₂ = Kernel.decode-γ* K₁
  in subst (λ x → ConPreorder._⊑_ (BulkBoundary.bnd BB₂) x Th₂)
           (sym (trans eq₁ (cong map∂ eq₂)))
           preserves-Th

-- Variant: derive `KernelHomFlowStable` from step preservation using μ-fusion.
--
-- Named as `ForHom` so downstream code can refer to it without reopening this
-- file’s local section.

module ForHom
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K₁ K₂ : Kernel Sig Q)
  (h : KernelHom K₁ K₂)
  where
  private
    module GT = Truth.GuardedCore {ℓ = ℓ}

    CP₁ : ConPreorder ℓ
    CP₁ = BulkBoundary.bnd (Kernel.BB K₁)

    CP₂ : ConPreorder ℓ
    CP₂ = BulkBoundary.bnd (Kernel.BB K₂)

  decode-mapCode-γ*≤Th*-fromFlow
    : (hf : KernelHomFlow K₁ K₂ h)
    → MuFusion.Kernel.KernelHomStabilisationAssumptions {K₁ = K₁} {K₂ = K₂} {h = h}
    → ConPreorder._⊑_ CP₂
        (Kernel.decode K₂ (KernelHom.mapCode h (Kernel.γ* K₁)))
        (Th⋆K K₂)
  decode-mapCode-γ*≤Th*-fromFlow hf A =
    decode-mapCode-γ*≤Th* K₁ K₂ h
      (MuFusion.Kernel.kernelHomFlowStable-from hf A)
