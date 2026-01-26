{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.LogicKernel.TensorEndo where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Adjunction using (MonoidalOps)
open import LogOS.Kernel.LogicKernel
open import LogOS.Kernel.LogicKernel.Endo

open import LogOS.Prelude.Product using (_×_; _,_)

-- Lax braiding/monoidality assumptions on the boundary monoidal preorder.

record LaxBraidingMBnd {ℓ : Level}
                       {Sig : LogOSSignature ℓ}
                       {Q   : QAdapter ℓ}
                       (K   : LogicKernel Sig Q)
                       : Set (lsuc ℓ) where
  open LogicKernel K
  open MonoidalOps MBnd using (_⊗_; I)
  field
    swapL→R : ∀ {c d} → ConPreorder._⊑_ (BulkBoundary.bnd BB) (c ⊗ d) (d ⊗ c)
    swapR→L : ∀ {c d} → ConPreorder._⊑_ (BulkBoundary.bnd BB) (d ⊗ c) (c ⊗ d)

record LaxMonoidalFlow {ℓ : Level}
                       {Sig : LogOSSignature ℓ}
                       {Q   : QAdapter ℓ}
                       (K   : LogicKernel Sig Q)
                       : Set (lsuc ℓ) where
  open LogicKernel K
  open MonoidalOps MBnd using (_⊗_; I)
  private
    FlowSat : ConPreorder.Con (BulkBoundary.bnd BB) → ConPreorder.Con (BulkBoundary.bnd BB)
    FlowSat = GTier.Flow G (GTier.sat G)
  field
    Flow⊗-lax : ∀ {c d} → ConPreorder._⊑_ (BulkBoundary.bnd BB)
                         (FlowSat (c ⊗ d))
                         ((FlowSat c) ⊗ (FlowSat d))
    Flow-I-lax : ConPreorder._⊑_ (BulkBoundary.bnd BB)
                (FlowSat I)
                I

record TensorLaws {ℓ : Level}
                  {Sig : LogOSSignature ℓ}
                  {Q   : QAdapter ℓ}
                  (K   : LogicKernel Sig Q)
                  : Set (lsuc ℓ) where
  field
    braiding : LaxBraidingMBnd K
    flow     : LaxMonoidalFlow K
  open LaxBraidingMBnd braiding public
  open LaxMonoidalFlow flow public

-- Canonical tensor endomaps on the boundary (right- and left-handed).

infixl 7 _⊗ᵣ_ _⊗ₗ_

_⊗ᵣ_
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
  → ConPreorder.Con (BulkBoundary.bnd (LogicKernel.BB K))
  → Endo K
_⊗ᵣ_ K d .Endo.fn c =
  let open LogicKernel K in
  MonoidalOps._⊗_ MBnd c d
_⊗ᵣ_ K d .Endo.mono {x} {y} p =
  let open LogicKernel K in
  let open MonoidalOps MBnd using (_⊗_; mono⊗) in
  let CP = BulkBoundary.bnd BB
      refl∂ = ConPreorder.refl CP {c = d}
  in mono⊗ p refl∂

_⊗ₗ_
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
  → ConPreorder.Con (BulkBoundary.bnd (LogicKernel.BB K))
  → Endo K
_⊗ₗ_ K c .Endo.fn d =
  let open LogicKernel K in
  MonoidalOps._⊗_ MBnd c d
_⊗ₗ_ K c .Endo.mono {x} {y} p =
  let open LogicKernel K in
  let open MonoidalOps MBnd using (_⊗_; mono⊗) in
  let CP = BulkBoundary.bnd BB
      refl∂ = ConPreorder.refl CP {c = c}
  in mono⊗ refl∂ p

-- Flow compatibility with tensor endomaps.

Flow⊗-endo-right
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : LogicKernel Sig Q)
    (TL : TensorLaws K)
    (d  : ConPreorder.Con (BulkBoundary.bnd (LogicKernel.BB K)))
  → _≤₂_ K ((Flow-Endo K) ∘E ((K ⊗ᵣ_) d))
             (((K ⊗ᵣ_) (Endo.fn (Flow-Endo K) d)) ∘E (Flow-Endo K))
Flow⊗-endo-right K TL d =
  let open TensorLaws TL in
  λ c → Flow⊗-lax {c} {d}

Flow⊗-endo-left
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : LogicKernel Sig Q)
    (TL : TensorLaws K)
    (c  : ConPreorder.Con (BulkBoundary.bnd (LogicKernel.BB K)))
  → _≤₂_ K ((Flow-Endo K) ∘E ((K ⊗ₗ_) c))
             (((K ⊗ₗ_) (Endo.fn (Flow-Endo K) c)) ∘E (Flow-Endo K))
Flow⊗-endo-left K TL c =
  let open TensorLaws TL in
  λ d → Flow⊗-lax {c = c} {d = d}

Flow⊗-infl-≤₂
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
    (d : ConPreorder.Con (BulkBoundary.bnd (LogicKernel.BB K)))
  → _≤₂_ K ((idEndo K) ∘E ((K ⊗ᵣ_) d))
             ((Flow-Endo K) ∘E ((K ⊗ᵣ_) d))
Flow⊗-infl-≤₂ K d =
  let open Endo2Cat K in
  λ c → whisker-right {f = idEndo K} {g = Flow-Endo K} {h = (K ⊗ᵣ_) d} (id≤Flow K) c

Flow⊗-infl-≤₂-left
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
    (c : ConPreorder.Con (BulkBoundary.bnd (LogicKernel.BB K)))
  → _≤₂_ K ((idEndo K) ∘E ((K ⊗ₗ_) c))
             ((Flow-Endo K) ∘E ((K ⊗ₗ_) c))
Flow⊗-infl-≤₂-left K c =
  let open Endo2Cat K in
  λ d → whisker-right {f = idEndo K} {g = Flow-Endo K} {h = (K ⊗ₗ_) c} (id≤Flow K) d
