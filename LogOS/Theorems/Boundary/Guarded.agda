{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Boundary.Guarded where

-- Guarded code theorems: decode-level preservation of γ* and guard naturality
-- under Kernel homomorphisms. Proven from Kernel fields (GuardedClosure and
-- KernelHomFlow) without additional postulates.

open import LogOS.Prelude
open import Data.Product using (_×_; _,_; fst; snd)

open import LogOS.Kernel
open import LogOS.Kernel.Hom
open import LogOS.Kernel.Endo
open import LogOS.Algebra.ConAlg
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter

-- If a Kernel hom preserves Flow (via KernelHomFlow), then the mapped
-- guarded fixed-point in the target decodes below Th* (lax preservation).

decode-mapCode-γ*≤Th*
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K₁ K₂ : Kernel Sig Q)
    (h  : KernelHom K₁ K₂)
    (ht : KernelHomFlow K₁ K₂ h)
  → ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K₂))
                 (Kernel.decode K₂ (KernelHom.mapCode h (Kernel.γ* K₁)))
                 (Th⋆K K₂)
decode-mapCode-γ*≤Th* {Sig = Sig} {Q = Q} K₁ K₂ h ht =
  let open Kernel K₁ renaming (BB to BB₁; GTruth to G₁)
      open Kernel K₂ renaming (BB to BB₂; GTruth to G₂)
      module GT0 = Truth.GuardedTruth Sig Q
      open KernelHom h
      open KernelHomFlow ht
      open GT0.GuardedClosure G₁ renaming (Th* to Th₁)
      open GT0.GuardedClosure G₂ renaming (Th* to Th₂)
      map∂ = ConAlgHom≡.map∂ (KernelHom.con-hom h)
      eq₁ : Kernel.decode K₂ (KernelHom.mapCode h (Kernel.γ* K₁)) ≡ map∂ (Kernel.decode K₁ (Kernel.γ* K₁))
      eq₁ = KernelHom.map-decode h (Kernel.γ* K₁)
      eq₂ : Kernel.decode K₁ (Kernel.γ* K₁) ≡ Th₁
      eq₂ = Kernel.decode-γ* K₁
  in subst (λ x → ConPoset._⊑_ (BulkBoundary.bnd BB₂) x Th₂)
           (sym (trans eq₁ (cong map∂ eq₂)))
           (GT0.FlowHom.preserves-Th flow-hom)
