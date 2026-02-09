{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Complexity.LanguageWitness where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_; ⊥)

open import LogOS.Prelude using (ℕ; zero; suc)
open import LogOS.Prelude using (_⊎_; inj₁; inj₂)
open import LogOS.Prelude using (Σ; _,_; proj₁; proj₂)

open import LogOS.Complexity.CookReckhow using (Finℓ; toNat; fzero; fsuc)
open import LogOS.Computation.Decider as D using (Decider; reindexDecider)
open import LogOS.Complexity.PolyBoundedCore as PB

-- TM-style “language” layer (input-indexed):
-- a language is just a predicate on an input type, and “TM-decidable” is the
-- existence of a total decider producing either a proof or a refutation.

DeciderI : ∀ {ℓI ℓ : Level} (Input : Set ℓI) (P : Input → Set ℓ) → Set (lsuc (ℓ ⊔ ℓI))
DeciderI Input P = Decider Input P

-- Reindex a decider along an input encoding.

reindexDeciderI
  : ∀ {ℓI₁ ℓI₂ ℓ}
    {Input₁ : Set ℓI₁} {Input₂ : Set ℓI₂}
    (f : Input₁ → Input₂)
    (P : Input₂ → Set ℓ)
  → DeciderI Input₂ P
  → DeciderI Input₁ (λ x → P (f x))
reindexDeciderI f P = reindexDecider f P

-- Poly-bounded witness systems for languages (Cook–Reckhow in input-indexed form).
-- This matches the usual NP certificate story: a decidable checker and a uniform
-- polynomial bound on witness size, plus completeness (every true instance has a
-- bounded witness).

record PolyBoundedWitnessSystem
  {ℓI ℓ : Level}
  (Input : Set ℓI)
  (P : Input → Set ℓ)
  : Set (lsuc (lsuc (ℓ ⊔ ℓI))) where
  field
    core : PB.PolyBoundedSystem Input P

  open PB.PolyBoundedSystem core public

-- Reindex witness systems along an input encoding.

reindexWitnessSystem
  : ∀ {ℓI₁ ℓI₂ ℓ}
    {Input₁ : Set ℓI₁} {Input₂ : Set ℓI₂}
    (f : Input₁ → Input₂)
    (P : Input₂ → Set ℓ)
  → PolyBoundedWitnessSystem Input₂ P
  → PolyBoundedWitnessSystem Input₁ (λ x → P (f x))
reindexWitnessSystem f P WS =
  record
    { core =
        record
          { size             = λ x → PolyBoundedWitnessSystem.size WS (f x)
          ; polyBound        = PolyBoundedWitnessSystem.polyBound WS
          ; Check            = λ n x → PolyBoundedWitnessSystem.Check WS n (f x)
          ; decCheck         = λ n x → PolyBoundedWitnessSystem.decCheck WS n (f x)
          ; sound            = λ n x → PolyBoundedWitnessSystem.sound WS n (f x)
          ; complete-bounded = λ x → PolyBoundedWitnessSystem.complete-bounded WS (f x)
          }
    }

-- Core bounded-witness lemma (Cook–Reckhow for languages):
-- a poly-bounded complete witness system yields a (TM-style) decider.

deciderFromWitnessSystem
  : ∀ {ℓI ℓ} {Input : Set ℓI}
    (P : Input → Set ℓ)
  → PolyBoundedWitnessSystem Input P
  → DeciderI Input P
deciderFromWitnessSystem P WS =
  PB.deciderFromPolyBoundedSystem P (PolyBoundedWitnessSystem.core WS)
