{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Eq where

-- Decode-level equality / decoded mutual refinement aliases for a given Kernel.
-- This helps keep meta-level `_≡_` distinct from the intended “same decoded meaning”
-- relations induced by `decode` (`_≃K_` and the preorder-safe `_≈K_`).

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.View
open import LogOS.Kernel
open import LogOS.Kernel.Graded using (GradedKernel)

module ForKernel {ℓ : Level}
                 {Sig : LogOSSignature ℓ}
                 {Q   : QAdapter ℓ}
                 (K   : Kernel Sig Q) where
  open Kernel K
  private
    CP = BulkBoundary.bnd BB
    RP = ConPreorder→RelPreorder CP
    decodeView : View Code RP
    decodeView = record { μ = decode }

  infix 4 _≃K_ _≈K_
  _≃K_ : Code → Code → Set ℓ
  γ₁ ≃K γ₂ = γ₁ ≃[ decodeView ] γ₂

  -- Decoded mutual refinement (in the boundary preorder).
  -- This is the preferred “same decoded meaning” notion when the boundary is only a preorder.
  _≈K_ : Code → Code → Set ℓ
  γ₁ ≈K γ₂ = γ₁ ≈[ decodeView ] γ₂

  refl≃K : ∀ γ → γ ≃K γ
  refl≃K γ = refl

  sym≃K  : ∀ {γ₁ γ₂} → γ₁ ≃K γ₂ → γ₂ ≃K γ₁
  sym≃K = sym

  trans≃K : ∀ {γ₁ γ₂ γ₃} → γ₁ ≃K γ₂ → γ₂ ≃K γ₃ → γ₁ ≃K γ₃
  trans≃K = trans

  refl≈K : ∀ γ → γ ≈K γ
  refl≈K γ = (ConPreorder.refl CP , ConPreorder.refl CP)

  sym≈K : ∀ {γ₁ γ₂} → γ₁ ≈K γ₂ → γ₂ ≈K γ₁
  sym≈K = ≈CP-sym {CP = CP}

  trans≈K : ∀ {γ₁ γ₂ γ₃} → γ₁ ≈K γ₂ → γ₂ ≈K γ₃ → γ₁ ≈K γ₃
  trans≈K = ≈CP-trans {CP = CP}

  ≃K→≈K : ∀ {γ₁ γ₂} → γ₁ ≃K γ₂ → γ₁ ≈K γ₂
  ≃K→≈K eq = ≃→≈[V] {V = decodeView} eq

-- Same aliases, but for `KernelLike` (shape-only kernels).
module ForKernelLike {ℓ : Level}
                     {Sig : LogOSSignature ℓ}
                     {Q   : QAdapter ℓ}
                     (K   : KernelLike Sig Q) where
  open KernelLike K
  private
    CP = BulkBoundary.bnd BB
    RP = ConPreorder→RelPreorder CP
    decodeView : View Code RP
    decodeView = record { μ = decode }

  infix 4 _≃K_ _≈K_
  _≃K_ : Code → Code → Set ℓ
  γ₁ ≃K γ₂ = γ₁ ≃[ decodeView ] γ₂

  _≈K_ : Code → Code → Set ℓ
  γ₁ ≈K γ₂ = γ₁ ≈[ decodeView ] γ₂

  refl≃K : ∀ γ → γ ≃K γ
  refl≃K γ = refl

  sym≃K  : ∀ {γ₁ γ₂} → γ₁ ≃K γ₂ → γ₂ ≃K γ₁
  sym≃K = sym

  trans≃K : ∀ {γ₁ γ₂ γ₃} → γ₁ ≃K γ₂ → γ₂ ≃K γ₃ → γ₁ ≃K γ₃
  trans≃K = trans

  refl≈K : ∀ γ → γ ≈K γ
  refl≈K γ = (ConPreorder.refl CP , ConPreorder.refl CP)

  sym≈K : ∀ {γ₁ γ₂} → γ₁ ≈K γ₂ → γ₂ ≈K γ₁
  sym≈K = ≈CP-sym {CP = CP}

  trans≈K : ∀ {γ₁ γ₂ γ₃} → γ₁ ≈K γ₂ → γ₂ ≈K γ₃ → γ₁ ≈K γ₃
  trans≈K = ≈CP-trans {CP = CP}

  ≃K→≈K : ∀ {γ₁ γ₂} → γ₁ ≃K γ₂ → γ₁ ≈K γ₂
  ≃K→≈K eq = ≃→≈[V] {V = decodeView} eq

-- Same aliases, but for `GradedKernel` (graded truth kernels).
module ForGradedKernel {ℓ : Level}
                       {Sig : LogOSSignature ℓ}
                       {Q   : QAdapter ℓ}
                       (K   : GradedKernel Sig Q) where
  open GradedKernel K
  private
    CP = BulkBoundary.bnd BB
    RP = ConPreorder→RelPreorder CP
    decodeView : View Code RP
    decodeView = record { μ = decode }

  infix 4 _≃K_ _≈K_
  _≃K_ : Code → Code → Set ℓ
  γ₁ ≃K γ₂ = γ₁ ≃[ decodeView ] γ₂

  _≈K_ : Code → Code → Set ℓ
  γ₁ ≈K γ₂ = γ₁ ≈[ decodeView ] γ₂

  refl≃K : ∀ γ → γ ≃K γ
  refl≃K γ = refl

  sym≃K  : ∀ {γ₁ γ₂} → γ₁ ≃K γ₂ → γ₂ ≃K γ₁
  sym≃K = sym

  trans≃K : ∀ {γ₁ γ₂ γ₃} → γ₁ ≃K γ₂ → γ₂ ≃K γ₃ → γ₁ ≃K γ₃
  trans≃K = trans

  refl≈K : ∀ γ → γ ≈K γ
  refl≈K γ = (ConPreorder.refl CP , ConPreorder.refl CP)

  sym≈K : ∀ {γ₁ γ₂} → γ₁ ≈K γ₂ → γ₂ ≈K γ₁
  sym≈K = ≈CP-sym {CP = CP}

  trans≈K : ∀ {γ₁ γ₂ γ₃} → γ₁ ≈K γ₂ → γ₂ ≈K γ₃ → γ₁ ≈K γ₃
  trans≈K = ≈CP-trans {CP = CP}

  ≃K→≈K : ∀ {γ₁ γ₂} → γ₁ ≃K γ₂ → γ₁ ≈K γ₂
  ≃K→≈K eq = ≃→≈[V] {V = decodeView} eq
