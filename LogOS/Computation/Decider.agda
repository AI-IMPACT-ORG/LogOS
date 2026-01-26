{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Computation.Decider where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_; _↔_; to; from)

open import LogOS.Prelude.Sum using (_⊎_)

-- A lightweight notion of a total decider for a predicate P.
--
-- The `decide` carrier is kept abstract (it may be P itself, a boolean witness,
-- a proof object, etc.) but must be total and logically equivalent to P via
-- soundness and completeness.

record Decider {ℓA ℓP : Level} (A : Set ℓA) (P : A → Set ℓP)
              : Set (lsuc (ℓA ⊔ ℓP)) where
  field
    decide : A → Set ℓP
    total  : ∀ x → decide x ⊎ ¬ decide x
    sound  : ∀ x → decide x → P x
    comp   : ∀ x → P x → decide x

open Decider public

-- Transport a decider across pointwise logical equivalence.
-- This keeps the computational carrier (`decide`) unchanged.

mapDecider
  : ∀ {ℓA ℓP}
    {A : Set ℓA}
    {P Q : A → Set ℓP}
  → (∀ x → P x ↔ Q x)
  → Decider A P
  → Decider A Q
mapDecider eq d =
  record
    { decide = Decider.decide d
    ; total  = Decider.total d
    ; sound  = λ x dx → to (eq x) (Decider.sound d x dx)
    ; comp   = λ x qx → Decider.comp d x (from (eq x) qx)
    }

-- Reindex a decider along a map of inputs (contravariant in the input).
-- This keeps the computational carrier unchanged, just precomposed with `f`.

reindexDecider
  : ∀ {ℓA₁ ℓA₂ ℓP}
    {A₁ : Set ℓA₁} {A₂ : Set ℓA₂}
    (f : A₁ → A₂)
    (P : A₂ → Set ℓP)
  → Decider A₂ P
  → Decider A₁ (λ x → P (f x))
reindexDecider f P d =
  record
    { decide = λ x → Decider.decide d (f x)
    ; total  = λ x → Decider.total d (f x)
    ; sound  = λ x dx → Decider.sound d (f x) dx
    ; comp   = λ x px → Decider.comp d (f x) px
    }

-- Decidability combinators (local, proof-relevant):
-- build a decision for a composite proposition from decisions for parts.

dec×
  : ∀ {ℓA ℓB}
    {A : Set ℓA} {B : Set ℓB}
  → (A ⊎ ¬ A)
  → (B ⊎ ¬ B)
  → (A × B) ⊎ ¬ (A × B)
dec× (inj₁ a) (inj₁ b) = inj₁ (a , b)
dec× (inj₁ a) (inj₂ nb) = inj₂ (λ ab → nb (snd ab))
dec× (inj₂ na) _ = inj₂ (λ ab → na (fst ab))
