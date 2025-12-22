{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.PolyBoundedCore where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import Data.Nat using (ℕ; suc)
open import Data.Sum using (_⊎_)
open import Data.Product using (Σ; _,_; proj₁; proj₂)

open import LogOS.Computation.Decider using (Decider)

import LogOS.Domain.Complexity.FiniteSearch as FS
open FS using (Finℓ; toNat)
module FSearch = FS.Search
open FSearch using (ExistsFin; searchFin)

-- A generic Cook–Reckhow style bounded-checking interface:
-- there is a decidable checker indexed by a natural “proof/witness size”,
-- with a polynomial (or otherwise specified) bound in terms of an input size.

record PolyBoundedSystem {ℓI ℓ : Level} (Input : Set ℓI) (P : Input → Set ℓ)
  : Set (lsuc (lsuc (ℓ ⊔ ℓI))) where
  field
    size : Input → ℕ
    polyBound : ℕ → ℕ

    Check    : ℕ → Input → Set ℓ
    decCheck : ∀ n x → Check n x ⊎ ¬ Check n x

    sound : ∀ n x → Check n x → P x

    complete-bounded
      : ∀ x → P x
      → Σ (Finℓ {ℓ} (suc (polyBound (size x))))
          (λ i → Check (toNat i) x)

open PolyBoundedSystem public

-- Bounded search yields a total decider (generic Cook–Reckhow lemma).

deciderFromPolyBoundedSystem
  : ∀ {ℓI ℓ} {Input : Set ℓI}
    (P : Input → Set ℓ)
  → PolyBoundedSystem Input P
  → Decider Input P
deciderFromPolyBoundedSystem {ℓ = ℓ} {Input = Input} P PS =
  record
    { decide = decide
    ; total  = total
    ; sound  = sound'
    ; comp   = comp'
    }
  where
    open PolyBoundedSystem PS renaming
      ( size             to sizeP
      ; polyBound        to polyBoundP
      ; Check            to CheckP
      ; decCheck         to decCheckP
      ; sound            to soundP
      ; complete-bounded to complete-boundedP
      )

    decide : Input → Set ℓ
    decide x = ExistsFin (λ i → CheckP (toNat i) x)

    total : ∀ x → decide x ⊎ ¬ decide x
    total x =
      searchFin (suc (polyBoundP (sizeP x)))
        (λ i → CheckP (toNat i) x)
        (λ i → decCheckP (toNat i) x)

    sound' : ∀ x → decide x → P x
    sound' x ex =
      let i  = proj₁ ex
          pr = proj₂ ex
      in soundP (toNat i) x pr

    comp' : ∀ x → P x → decide x
    comp' x px = complete-boundedP x px
