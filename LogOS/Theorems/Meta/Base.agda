{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.Base where

open import LogOS.Prelude
open import Data.Product as DP using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel
open import LogOS.Computation.FromKernel
open import LogOS.Computation.Decider as Dec using (Decider)
open import LogOS.Syntax.Prop using (¬_; _↔_)

-- Computation-based semantics: abstract equivalence on codes.

record CompSem {ℓ : Level}
               (Sig : LogOSSignature ℓ)
               (Q   : QAdapter ℓ)
               (K   : Kernel Sig Q)
               : Set (lsuc ℓ) where
  field
    eqCode : Kernel.Code K → Kernel.Code K → Set ℓ

-- Extensionality and non-triviality for properties over codes (computation view).

ExtensionalC
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
    (S : CompSem Sig Q K)
    (P : Kernel.Code K → Set ℓ)
  → Set ℓ
ExtensionalC S P = ∀ γ₁ γ₂ → CompSem.eqCode S γ₁ γ₂ → (P γ₁ → P γ₂)

NonTrivialC
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
    (P : Kernel.Code K → Set ℓ)
  → Set ℓ
NonTrivialC {K = K} P = DP._×_ (Σ (Kernel.Code K) (λ γ → P γ)) (Σ (Kernel.Code K) (λ γ → ¬ P γ))

-- A very lightweight notion of a decider-by-code (computation view).
-- In practice, instantiate with a concrete total computation over codes.

record DeciderC {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} {K : Kernel Sig Q}
                (P : Kernel.Code K → Set ℓ)
                : Set (lsuc ℓ) where
  field
    core : Decider (Kernel.Code K) P

  open Decider core public

  -- Convenience wrappers (keep the meaning explicit at call sites).
  toDecider : Decider (Kernel.Code K) P
  toDecider = core

mkDeciderC
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} {K : Kernel Sig Q}
    {P : Kernel.Code K → Set ℓ}
  → Decider (Kernel.Code K) P
  → DeciderC {K = K} P
mkDeciderC d = record { core = d }

-- Transport a kernel decider across pointwise logical equivalence.
mapDeciderC
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} {K : Kernel Sig Q}
    {P P′ : Kernel.Code K → Set ℓ}
  → (∀ γ → P γ ↔ P′ γ)
  → DeciderC {K = K} P
  → DeciderC {K = K} P′
mapDeciderC eq d =
  mkDeciderC (Dec.mapDecider eq (DeciderC.toDecider d))
