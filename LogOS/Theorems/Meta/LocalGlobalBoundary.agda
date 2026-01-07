{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.LocalGlobalBoundary where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_; _↔_)

open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)

import LogOS.Theorems.Meta.LimitPublicisation as LP
import LogOS.Computation.SemiDecider as SD

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

-- Cofinal schedule indexed by ℕ.
--
-- This variant avoids universe-level restrictions on the schedule type, and is
-- the shape needed to build semi-decision procedures (bounded search over ℕ).

Cofinalℕ
  : ∀ {ℓA}
    {A : Set ℓA}
  → LP.Preorder A
  → (ℕ → A)
  → Set ℓA
Cofinalℕ PA u = ∀ a → Σ ℕ (λ n → LP.Preorder._≤_ PA a (u n))

-- Join-colimits along a cofinal ℕ-schedule.
Join-cofinalℕ
  : ∀ {ℓT ℓA ℓX}
    {A : Set ℓA} {X : Set ℓX}
    (PA : LP.Preorder A)
    (u  : ℕ → A)
    (cof : Cofinalℕ PA u)
    (Pred : A → X → Set ℓT)
    (mono : ∀ {i j} → LP.Preorder._≤_ PA i j → ∀ {x} → Pred i x → Pred j x)
  → ∀ {x} → Join Pred x ↔ Σ ℕ (λ n → Pred (u n) x)
Join-cofinalℕ PA u cof Pred mono {x} =
  record
    { to   = λ ex →
        let i    = proj₁ ex
            pr   = proj₂ ex
            hit  = cof i
            n    = proj₁ hit
            i≤un = proj₂ hit
        in n , mono i≤un pr
    ; from = λ ex → u (proj₁ ex) , proj₂ ex
    }

-- Build a semi-decision procedure for the Join predicate using a cofinal schedule.
--
-- Reading: if global truth is “true at some resource index”, and we can
-- enumerate a cofinal chain of indices with decidable steps, then global truth
-- is semi-decidable.

semiDeciderJoin
  : ∀ {ℓT ℓA ℓX}
    {A : Set ℓA} {X : Set ℓX}
    (PA : LP.Preorder A)
    (u  : ℕ → A)
    (cof : Cofinalℕ PA u)
    (Pred : A → X → Set ℓT)
    (mono : ∀ {i j} → LP.Preorder._≤_ PA i j → ∀ {x} → Pred i x → Pred j x)
    (decPred : ∀ n x → Pred (u n) x ⊎ ¬ Pred (u n) x)
  → SD.SemiDecider X (Join Pred)
semiDeciderJoin PA u cof Pred mono decPred =
  record
    { Approx      = λ n x → Pred (u n) x
    ; decApprox   = decPred
    ; soundApprox = λ n x pr → u n , pr
    ; complete    = λ x ex →
        let i    = proj₁ ex
            pr   = proj₂ ex
            hit  = cof i
            n    = proj₁ hit
            i≤un = proj₂ hit
        in n , mono i≤un pr
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
