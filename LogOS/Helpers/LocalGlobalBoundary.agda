{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Helpers.LocalGlobalBoundary where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)

open import Data.Product using (Σ; _,_; proj₁; proj₂)

import LogOS.Theorems.Meta.LimitPublicisation as LP

-- One shared “root shape” behind many developments in LogOS:
--
-- - Local structure is indexed by a preorder of “resources/approximants” A.
-- - A *meet/Π-limit* asks for evidence at all indices (global stability / regulator-independence).
-- - A *join/Σ-colimit* asks for evidence at some index (global existence / proof search).
-- - Cofinal schedules let you replace “all indices” or “some index” with a chain u : B → A,
--   provided the indexed family is monotone in the appropriate direction.

Meet
  : ∀ {ℓT ℓA ℓX}
    {A : Set ℓA} {X : Set ℓX}
  → (A → X → Set ℓT) → X → Set (ℓT ⊔ ℓA)
Meet = LP.LimitTruth

Join
  : ∀ {ℓT ℓA ℓX}
    {A : Set ℓA} {X : Set ℓX}
  → (A → X → Set ℓT) → X → Set (ℓT ⊔ ℓA)
Join Pred x = Σ _ (λ i → Pred i x)

Meet-cofinal = LP.LimitTruth-cofinal

-- Dual to `LP.LimitTruth-cofinal`.
--
-- If the family is monotone (increasing) in the index, then existence at *some* index
-- is equivalent to existence along a cofinal schedule.
Join-cofinal
  : ∀ {ℓT ℓA ℓX}
    {A : Set ℓA} {B : Set ℓA} {X : Set ℓX}
    (PA : LP.Preorder A)
    (u  : B → A)
    (cof : LP.Cofinal PA u)
    (Pred : A → X → Set ℓT)
    (mono : ∀ {i j} → LP.Preorder._≤_ PA i j → ∀ {x} → Pred i x → Pred j x)
  → ∀ {x} → Join Pred x ↔ Join (λ b → Pred (u b)) x
Join-cofinal PA u cof Pred mono {x} =
  record
    { to   = λ ex →
        let i    = proj₁ ex
            pr   = proj₂ ex
            hit  = LP.Cofinal.hit cof i
            b    = proj₁ hit
            i≤ub = proj₂ hit
        in b , mono i≤ub pr
    ; from = λ ex → u (proj₁ ex) , proj₂ ex
    }

-- A “closure-step builder” for domain authors:
-- extend evidence from a cofinal schedule to full meet/limit evidence.
meetFromCofinal
  : ∀ {ℓT ℓA ℓX}
    {A : Set ℓA} {B : Set ℓA} {X : Set ℓX}
    (PA : LP.Preorder A)
    (u  : B → A)
    (cof : LP.Cofinal PA u)
    (Pred : A → X → Set ℓT)
    (antiMono : ∀ {i j} → LP.Preorder._≤_ PA i j → ∀ {x} → Pred j x → Pred i x)
    {x : X}
  → (∀ b → Pred (u b) x)
  → ∀ a → Pred a x
meetFromCofinal PA u cof Pred antiMono {x} holdsᵇ a =
  let hit  = LP.Cofinal.hit cof a
      b    = proj₁ hit
      a≤ub = proj₂ hit
  in antiMono a≤ub (holdsᵇ b)
