{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Opacity.Distinguishability where

-- Finite, explicit families on a carrier together with separation under a
-- chosen observation.

open import LogOS.Prelude
open import LogOS.Prelude.Fin using (Fin; _≢_)
open import LogOS.Prelude.FiniteFamily using (FiniteFamily)
open import LogOS.LT.ConPreorder using (ConPreorder)
open import LogOS.LT.View using (View; _≈[_]_)

ObservedFamily : ∀ {ℓX} (X : Set ℓX) → Set ℓX
ObservedFamily X = FiniteFamily X

size : ∀ {ℓX} {X : Set ℓX} → ObservedFamily X → ℕ
size = FiniteFamily.size

at : ∀ {ℓX} {X : Set ℓX} → (xs : ObservedFamily X) → Fin (size xs) → X
at = FiniteFamily.at

map
  : ∀ {ℓX ℓY} {X : Set ℓX} {Y : Set ℓY}
  → (X → Y)
  → ObservedFamily X
  → ObservedFamily Y
map f xs =
  record
    { size = size xs
    ; at = λ i → f (at xs i)
    }

record DistinguishableFamily
  {ℓX ℓC ℓR : Level}
  {X : Set ℓX}
  {O : ConPreorder ℓC ℓR}
  (V : View X O)
  : Set (ℓX ⊔ ℓR) where
  field
    family : ObservedFamily X
    separated : ∀ i j → i ≢ j → ¬ (at family i ≈[ V ] at family j)

open DistinguishableFamily public
