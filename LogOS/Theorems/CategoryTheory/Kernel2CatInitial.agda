{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.CategoryTheory.Kernel2CatInitial where

-- Initiality in the refinement 2-category: the fold map is unique up to
-- pointwise refinement (not just decode-level equality).

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Con.Rewrite as ConRewrite
open import LogOS.Minimal.World
open import LogOS.Free.Constraints as Free

open import LogOS.Kernel
open import LogOS.Kernel.ConAlgOf using (conAlgOf)
open import LogOS.Kernel.Initial
import LogOS.Kernel.Hom2Cat as KH₂

module InitialRefinement {ℓ : Level}
                         (Sig : LogOSSignature ℓ)
                         (Q   : QAdapter ℓ)
                         (HWorld : Worlds.WorldH Sig Q) where
  private
    IK : InitialKernel Sig Q
    IK = build Sig Q HWorld

  open InitialKernel IK

  KernelHom₁ : Kernel Sig Q → Kernel Sig Q → Set (lsuc (lsuc ℓ))
  KernelHom₁ = KH₂.KernelHom₁ {Sig = Sig} {Q = Q}

  infix 4 _⇒_ _≈_
  _⇒_ : ∀ {K₁ K₂ : Kernel Sig Q} → KernelHom₁ K₁ K₂ → KernelHom₁ K₁ K₂ → Set ℓ
  _⇒_ {K₁ = K₁} {K₂ = K₂} = KH₂._⇒_ {Sig = Sig} {Q = Q} {K₁ = K₁} {K₂ = K₂}

  _≈_ : ∀ {K₁ K₂ : Kernel Sig Q} → KernelHom₁ K₁ K₂ → KernelHom₁ K₁ K₂ → Set ℓ
  _≈_ {K₁ = K₁} {K₂ = K₂} = KH₂._≈_ {Sig = Sig} {Q = Q} {K₁ = K₁} {K₂ = K₂}

  foldK₁ : ∀ (K : Kernel Sig Q) → KernelHom₁ (FreeK) K
  foldK₁ K =
    record
      { hom   = foldK K
      ; mono∂ = Free.interp∂-mono (conAlgOf K)
      }

  foldK⇒ : ∀ (K : Kernel Sig Q) (h : KernelHom₁ (FreeK) K) → foldK₁ K ⇒ h
  foldK⇒ K h γ =
    let
      hK = KH₂.homKernel {Sig = Sig} {Q = Q} {K₁ = FreeK} {K₂ = K} h
      _ , _ , eqγ = InitialKernel.unique≃ IK K hK
      CP = BulkBoundary.bnd (Kernel.BB K)
      module R = ConRewrite.For CP
    in
    R.substR (eqγ γ) (ConPoset.refl CP)

  foldK⇐ : ∀ (K : Kernel Sig Q) (h : KernelHom₁ (FreeK) K) → h ⇒ foldK₁ K
  foldK⇐ K h γ =
    let
      hK = KH₂.homKernel {Sig = Sig} {Q = Q} {K₁ = FreeK} {K₂ = K} h
      _ , _ , eqγ = InitialKernel.unique≃ IK K hK
      CP = BulkBoundary.bnd (Kernel.BB K)
      module R = ConRewrite.For CP
    in
    R.substR (sym (eqγ γ)) (ConPoset.refl CP)

  foldK≈ : ∀ (K : Kernel Sig Q) (h : KernelHom₁ (FreeK) K) → foldK₁ K ≈ h
  foldK≈ K h = foldK⇒ K h , foldK⇐ K h
