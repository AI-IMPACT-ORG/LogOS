{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.Applications.GRH.HPGRHLimit where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel
open import LogOS.Kernel.Endo

open import LogOS.Domain.Opacity.NumberTheory.HP.Interface as HPi
open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann

-- Resource index (preorder) to model increasing approximation budgets

record ResIdx {ℓ : Level} : Set (lsuc ℓ) where
  infix 4 _≤I_
  field
    I      : Set ℓ
    _≤I_   : I → I → Set ℓ
    reflI  : ∀ {i}     → _≤I_ i i
    transI : ∀ {i j k} → _≤I_ i j → _≤I_ j k → _≤I_ i k

-- Approximate Hilbert–Pólya family with coherent embeddings and an operator limit

record ApproxHP {ℓ}
                (Sig : LogOSSignature ℓ)
                (Q   : QAdapter ℓ)
                (K   : Kernel Sig Q)
                : Set (lsuc (lsuc ℓ)) where
  open Kernel K
  module Gd = Truth.GuardedTruth Sig Q
  field
    idx : ResIdx {ℓ}

  module I = ResIdx idx

  field
    HP    : I.I → HPi.HPInterface K

  -- Shorthand projections for per-index structures
  Hᵢ : I.I → Set ℓ
  Hᵢ i = HPi.HPInterface.H (HP i)

  Opᵢ : (i : I.I) → Hᵢ i → Hᵢ i
  Opᵢ i = HPi.HPInterface.Op (HP i)

  embedᵢ : (i : I.I) → ConPoset.Con (BulkBoundary.bnd BB) → Hᵢ i
  embedᵢ i = HPi.HPInterface.embed (HP i)

  field
    -- Coherent "upgrade" maps along the resource index
    upH    : ∀ {i j} → I._≤I_ i j → Hᵢ i → Hᵢ j
    up-Op  : ∀ {i j} (hij : I._≤I_ i j) (h : Hᵢ i)
           → upH hij (Opᵢ i h) ≡ Opᵢ j (upH hij h)
    up-emb : ∀ {i j} (hij : I._≤I_ i j) (c : ConPoset.Con (BulkBoundary.bnd BB))
           → upH hij (embedᵢ i c) ≡ embedᵢ j c

  field
    -- Operator limit data
    H∞      : Set ℓ
    Op∞     : H∞ → H∞
    embed∞  : ConPoset.Con (BulkBoundary.bnd BB) → H∞
    lim     : (i : I.I) → Hᵢ i → H∞
    lim-Op  : ∀ i h → lim i (Opᵢ i h) ≡ Op∞ (lim i h)
    lim-emb : ∀ i c → lim i (embedᵢ i c) ≡ embed∞ c
    -- Intertwining at the limit (operator is truth under the embedding)
    intertwine∞ : ∀ c → embed∞ (Endo.fn (Flow-Endo K) c)
                        ≡ Op∞ (embed∞ c)

-- Limit-level GRH assumptions and consequence

record HP∞GRHAssumptions {ℓ}
                         {Sig : LogOSSignature ℓ}
                         {Q   : QAdapter ℓ}
                         (K   : Kernel Sig Q)
                         (AHP : ApproxHP Sig Q K)
                         (RS  : RiemannSpectral)
                         : Set (lsuc ℓ) where
  open Kernel K
  open ApproxHP AHP
  open RiemannSpectral RS
  field
    c : Spectral → ConPoset.Con (BulkBoundary.bnd BB)
    Op∞FixedOnZero : ∀ s → NontrivialZero s → Op∞ (embed∞ (c s)) ≡ embed∞ (c s)
    Op∞Fixed→OnLine : ∀ s → Op∞ (embed∞ (c s)) ≡ embed∞ (c s) → OnLine s

-- Derive GRH_Without_Vacuity_Guards at the boundary from the limit operator

GRH_Without_Vacuity_Guards_via_HP∞
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K   : Kernel Sig Q)
    (AHP : ApproxHP Sig Q K)
    (RS  : RiemannSpectral)
    (A   : HP∞GRHAssumptions K AHP RS)
  → ∀ s → RiemannSpectral.NontrivialZero RS s → RiemannSpectral.OnLine RS s
GRH_Without_Vacuity_Guards_via_HP∞ K AHP RS A s nz = HP∞GRHAssumptions.Op∞Fixed→OnLine A s (HP∞GRHAssumptions.Op∞FixedOnZero A s nz)

-- Helper: if each finite approximation is Op-fixed on zeros, the limit is Op∞-fixed

derive-Op∞Fixed
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K   : Kernel Sig Q)
    (AHP : ApproxHP Sig Q K)
    (RS  : RiemannSpectral)
    (c   : RiemannSpectral.Spectral RS → ConPoset.Con (BulkBoundary.bnd (Kernel.BB K)))
    (i   : (let open ApproxHP AHP in ResIdx.I (idx)))
    → (∀ i s → RiemannSpectral.NontrivialZero RS s
             → HPi.HPInterface.Op (ApproxHP.HP AHP i) (HPi.HPInterface.embed (ApproxHP.HP AHP i) (c s))
               ≡ HPi.HPInterface.embed (ApproxHP.HP AHP i) (c s))
    → ∀ s → RiemannSpectral.NontrivialZero RS s
      → ApproxHP.Op∞ AHP (ApproxHP.embed∞ AHP (c s)) ≡ ApproxHP.embed∞ AHP (c s)
derive-Op∞Fixed K AHP RS c i all-fix s nz =
  let open ApproxHP AHP in
  trans (cong Op∞ (sym (lim-emb i (c s))))
    (trans (sym (lim-Op i (embedᵢ i (c s))))
      (trans (cong (λ x → lim i x) (all-fix i s nz)) (lim-emb i (c s))))
  where
  open import LogOS.Prelude using (_≡_; sym; cong; trans)
