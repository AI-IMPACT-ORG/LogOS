{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.CategoryTheory.Kernel2Cat where

-- A lightweight 2-category packaging for kernels:
-- - 1-cells: kernel morphisms equipped with boundary monotonicity
-- - 2-cells: pointwise refinement on decoded code maps
--
-- See `LogOS.Kernel.Hom2Cat` for the underlying operations.

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel
import LogOS.Kernel.Hom2Cat as KH₂
open import LogOS.Theorems.CategoryTheory.WrapperCore public
  renaming (Ref2Cat to Kernel2Cat)

Kernel2Cat-instance
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
  → Kernel2Cat Sig Q
Kernel2Cat-instance Sig Q =
  record
    { Obj = Kernel Sig Q
    ; Hom = KH₂.KernelHom₁ {Sig = Sig} {Q = Q}
    ; _∘_ = λ g f → KH₂._∘₁_ {Sig = Sig} {Q = Q} g f
    ; id  = λ {A} → KH₂.idKernelHom₁ {Sig = Sig} {Q = Q} A
    ; _⇒_ = λ {A} {B} → KH₂._⇒_ {Sig = Sig} {Q = Q} {K₁ = A} {K₂ = B}
    ; id⇒ = λ {A} {B} f → KH₂.refl⇒ {Sig = Sig} {Q = Q} {K₁ = A} {K₂ = B} f
    ; _∙_ = λ {A} {B} {f} {g} {h} fg gh →
        KH₂.trans⇒ {Sig = Sig} {Q = Q} {K₁ = A} {K₂ = B} {f = f} {g = g} {h = h} fg gh
    ; whiskerL = λ {A} {B} {C} g {f} {f'} ff' →
        KH₂.whiskerL {Sig = Sig} {Q = Q} {K₁ = A} {K₂ = B} {K₃ = C} g {f = f} {f' = f'} ff'
    ; whiskerR = λ {A} {B} {C} {g} {g'} f gg' →
        KH₂.whiskerR {Sig = Sig} {Q = Q} {K₁ = A} {K₂ = B} {K₃ = C} {g = g} {g' = g'} f gg'
    ; _⊙_      = λ {A} {B} {C} {f} {f'} {g} {g'} ff' gg' →
        KH₂._⊙_ {Sig = Sig} {Q = Q} {K₁ = A} {K₂ = B} {K₃ = C} {f = f} {f' = f'} {g = g} {g' = g'} ff' gg'
    }
