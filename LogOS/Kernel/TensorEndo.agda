{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.TensorEndo where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Adjunction
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel
open import LogOS.Kernel.Endo

open import Data.Product using (_×_; _,_)

-- Lax braiding/monoidality assumptions on the boundary monoidal poset.

record LaxBraidingMBnd {ℓ : Level}
                       {Sig : LogOSSignature ℓ}
                       {Q   : QAdapter ℓ}
                       (K   : Kernel Sig Q)
                       : Set (lsuc ℓ) where
  open Kernel K
  open MonoidalPoset MBnd using (_⊗_; I)
  field
    swapL→R : ∀ {c d} → ConPoset._⊑_ (BulkBoundary.bnd BB) (c ⊗ d) (d ⊗ c)
    swapR→L : ∀ {c d} → ConPoset._⊑_ (BulkBoundary.bnd BB) (d ⊗ c) (c ⊗ d)

record LaxMonoidalFlow {ℓ : Level}
                       {Sig : LogOSSignature ℓ}
                       {Q   : QAdapter ℓ}
                       (K   : Kernel Sig Q)
                       : Set (lsuc ℓ) where
  open Kernel K
  open MonoidalPoset MBnd using (_⊗_; I)
  field
    Flow⊗-lax : ∀ {c d} → ConPoset._⊑_ (BulkBoundary.bnd BB)
                         (Truth.GuardedCore.GuardedClosure.Flow GTruth (c ⊗ d))
                         ((Truth.GuardedCore.GuardedClosure.Flow GTruth c)
                           ⊗ (Truth.GuardedCore.GuardedClosure.Flow GTruth d))
    Flow-I-lax : ConPoset._⊑_ (BulkBoundary.bnd BB)
                (Truth.GuardedCore.GuardedClosure.Flow GTruth I)
                I

-- Canonical tensor endomaps on the boundary (right- and left-handed).

infixl 7 _⊗ᵣ_ _⊗ₗ_

_⊗ᵣ_
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    → ConPoset.Con (BulkBoundary.bnd (Kernel.BB K))
    → Endo K
_⊗ᵣ_ K d .Endo.fn c =
  let open Kernel K in
  MonoidalPoset._⊗_ MBnd c d
_⊗ᵣ_ K d .Endo.mono {x} {y} p =
  let open Kernel K in
  let open MonoidalPoset MBnd using (_⊗_; mono⊗) in
  let refl∂ = ConPoset.refl (BulkBoundary.bnd BB) in
  mono⊗ p refl∂

_⊗ₗ_
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    → ConPoset.Con (BulkBoundary.bnd (Kernel.BB K))
    → Endo K
_⊗ₗ_ K c .Endo.fn d =
  let open Kernel K in
  MonoidalPoset._⊗_ MBnd c d
_⊗ₗ_ K c .Endo.mono {x} {y} p =
  let open Kernel K in
  let open MonoidalPoset MBnd using (_⊗_; mono⊗) in
  let refl∂ = ConPoset.refl (BulkBoundary.bnd BB) in
  mono⊗ refl∂ p

-- Flow compatibility with tensor endomaps.

Flow⊗-endo-right
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (LM : LaxMonoidalFlow K)
    (d  : ConPoset.Con (BulkBoundary.bnd (Kernel.BB K)))
  → _≤₂_ K ((Flow-Endo K) ∘E ((K ⊗ᵣ_) d))
             (((K ⊗ᵣ_) (Endo.fn (Flow-Endo K) d)) ∘E (Flow-Endo K))
Flow⊗-endo-right K LM d =
  let open Kernel K in
  let open LaxMonoidalFlow LM in
  λ c → Flow⊗-lax {c} {d}

Flow⊗-endo-left
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (LM : LaxMonoidalFlow K)
    (c  : ConPoset.Con (BulkBoundary.bnd (Kernel.BB K)))
  → _≤₂_ K ((Flow-Endo K) ∘E ((K ⊗ₗ_) c))
             (((K ⊗ₗ_) (Endo.fn (Flow-Endo K) c)) ∘E (Flow-Endo K))
Flow⊗-endo-left K LM c =
  let open Kernel K in
  let open LaxMonoidalFlow LM in
  λ d → Flow⊗-lax {c = c} {d = d}

Flow⊗-infl-≤₂
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (d : ConPoset.Con (BulkBoundary.bnd (Kernel.BB K)))
  → _≤₂_ K ((idEndo K) ∘E ((K ⊗ᵣ_) d))
             ((Flow-Endo K) ∘E ((K ⊗ᵣ_) d))
Flow⊗-infl-≤₂ K d =
  let open Endo2Cat K in
  λ c → whisker-right {f = idEndo K} {g = Flow-Endo K} {h = (K ⊗ᵣ_) d} (id≤Flow K) c

Flow⊗-infl-≤₂-left
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (c : ConPoset.Con (BulkBoundary.bnd (Kernel.BB K)))
  → _≤₂_ K ((idEndo K) ∘E ((K ⊗ₗ_) c))
             ((Flow-Endo K) ∘E ((K ⊗ₗ_) c))
Flow⊗-infl-≤₂-left K c =
  let open Endo2Cat K in
  λ d → whisker-right {f = idEndo K} {g = Flow-Endo K} {h = (K ⊗ₗ_) c} (id≤Flow K) d
