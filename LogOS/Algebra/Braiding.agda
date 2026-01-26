{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Algebra.Braiding where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Adjunction
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel
open import LogOS.Kernel.Endo
open import LogOS.Kernel.TensorEndo public using
  ( TensorLaws
  ; _⊗ᵣ_; _⊗ₗ_
  ; Flow⊗-endo-right; Flow⊗-endo-left
  ; Flow⊗-infl-≤₂; Flow⊗-infl-≤₂-left
  )
open import LogOS.Prelude.Product using (_×_; _,_)

-- Consequences: swap respect and fixed-point closure for Flow under tensor.

Flow-respects-swap
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (TL : TensorLaws K)
  → ∀ {c d} →
    ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K))
      (Endo.fn (Flow-Endo K) (MonoidalOps._⊗_ (Kernel.MBnd K) c d))
      (Endo.fn (Flow-Endo K) (MonoidalOps._⊗_ (Kernel.MBnd K) d c))
Flow-respects-swap K TL {c} {d} =
  let open Kernel K in
  let open TensorLaws TL in
  Endo.mono (Flow-Endo K) swapL→R

Flow-respects-swap-both
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (TL : TensorLaws K)
  → ∀ {c d} →
    ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K))
      (Endo.fn (Flow-Endo K) (MonoidalOps._⊗_ (Kernel.MBnd K) c d))
      (Endo.fn (Flow-Endo K) (MonoidalOps._⊗_ (Kernel.MBnd K) d c))
    ×
    ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K))
      (Endo.fn (Flow-Endo K) (MonoidalOps._⊗_ (Kernel.MBnd K) d c))
      (Endo.fn (Flow-Endo K) (MonoidalOps._⊗_ (Kernel.MBnd K) c d))
Flow-respects-swap-both K TL {c} {d} =
  let open Kernel K in
  let open TensorLaws TL in
  Endo.mono (Flow-Endo K) swapL→R ,
  Endo.mono (Flow-Endo K) swapR→L

Fixed-under-⊗
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (TL : TensorLaws K)
  → ∀ {c d} →
    Endo.fn (Flow-Endo K) c ≡ c →
    Endo.fn (Flow-Endo K) d ≡ d →
    ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K))
      (Endo.fn (Flow-Endo K) (MonoidalOps._⊗_ (Kernel.MBnd K) c d))
      (MonoidalOps._⊗_ (Kernel.MBnd K) c d)
    ×
    ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K))
      (MonoidalOps._⊗_ (Kernel.MBnd K) c d)
      (Endo.fn (Flow-Endo K) (MonoidalOps._⊗_ (Kernel.MBnd K) c d))
Fixed-under-⊗ K TL {c} {d} fc fd =
  let open Kernel K in
  let open TensorLaws TL in
  let F   = Endo.fn (Flow-Endo K) in
  let open MonoidalOps MBnd using (_⊗_) in
  let left : ConPreorder._⊑_ (BulkBoundary.bnd BB) (F (c ⊗ d)) (c ⊗ d)
      left =
        let flow≤tensor = Flow⊗-endo-right K TL d c in
        subst (λ x → ConPreorder._⊑_ (BulkBoundary.bnd BB) (F (c ⊗ d)) x)
              (cong₂ _⊗_ fc fd)
              flow≤tensor
      right : ConPreorder._⊑_ (BulkBoundary.bnd BB) (c ⊗ d) (F (c ⊗ d))
      right = Flow⊗-infl-≤₂ K d c
  in left , right
