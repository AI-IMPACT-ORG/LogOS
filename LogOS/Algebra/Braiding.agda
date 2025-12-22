{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
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
  ( LaxBraidingMBnd
  ; LaxMonoidalFlow
  ; _⊗ᵣ_; _⊗ₗ_
  ; Flow⊗-endo-right; Flow⊗-endo-left
  ; Flow⊗-infl-≤₂; Flow⊗-infl-≤₂-left
  )
open import Data.Product using (_×_; _,_)

-- Consequences: swap respect and fixed-point closure for Flow under tensor.

Flow-respects-swap
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (Br : LaxBraidingMBnd K)
  → ∀ {c d} →
    ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K))
      (Endo.fn (Flow-Endo K) (MonoidalPoset._⊗_ (Kernel.MBnd K) c d))
      (Endo.fn (Flow-Endo K) (MonoidalPoset._⊗_ (Kernel.MBnd K) d c))
Flow-respects-swap K Br {c} {d} =
  let open Kernel K in
  let open LaxBraidingMBnd Br in
  Endo.mono (Flow-Endo K) swapL→R

Flow-respects-swap-both
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (Br : LaxBraidingMBnd K)
  → ∀ {c d} →
    ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K))
      (Endo.fn (Flow-Endo K) (MonoidalPoset._⊗_ (Kernel.MBnd K) c d))
      (Endo.fn (Flow-Endo K) (MonoidalPoset._⊗_ (Kernel.MBnd K) d c))
    ×
    ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K))
      (Endo.fn (Flow-Endo K) (MonoidalPoset._⊗_ (Kernel.MBnd K) d c))
      (Endo.fn (Flow-Endo K) (MonoidalPoset._⊗_ (Kernel.MBnd K) c d))
Flow-respects-swap-both K Br {c} {d} =
  let open Kernel K in
  let open LaxBraidingMBnd Br in
  Endo.mono (Flow-Endo K) swapL→R ,
  Endo.mono (Flow-Endo K) swapR→L

Fixed-under-⊗
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (LM : LaxMonoidalFlow K)
  → ∀ {c d} →
    Endo.fn (Flow-Endo K) c ≡ c →
    Endo.fn (Flow-Endo K) d ≡ d →
    ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K))
      (Endo.fn (Flow-Endo K) (MonoidalPoset._⊗_ (Kernel.MBnd K) c d))
      (MonoidalPoset._⊗_ (Kernel.MBnd K) c d)
    ×
    ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K))
      (MonoidalPoset._⊗_ (Kernel.MBnd K) c d)
      (Endo.fn (Flow-Endo K) (MonoidalPoset._⊗_ (Kernel.MBnd K) c d))
Fixed-under-⊗ K LM {c} {d} fc fd =
  let open Kernel K in
  let open LaxMonoidalFlow LM in
  let F   = Endo.fn (Flow-Endo K) in
  let open MonoidalPoset MBnd using (_⊗_) in
  let left : ConPoset._⊑_ (BulkBoundary.bnd BB) (F (c ⊗ d)) (c ⊗ d)
      left =
        let flow≤tensor = Flow⊗-endo-right K LM d c in
        subst (λ x → ConPoset._⊑_ (BulkBoundary.bnd BB) (F (c ⊗ d)) x)
              (cong₂ _⊗_ fc fd)
              flow≤tensor
      right : ConPoset._⊑_ (BulkBoundary.bnd BB) (c ⊗ d) (F (c ⊗ d))
      right = Flow⊗-infl-≤₂ K d c
  in left , right
