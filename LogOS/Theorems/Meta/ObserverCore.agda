{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.ObserverCore where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; intro; to; from; ¬_)
open import Data.Product using (Σ; _,_; _×_)

-- Generic “observer semantics” core:
-- - a code language `Code`,
-- - a decode view `decode : Code → Dec`,
-- - a one-step dynamics `step : Code → Code`,
-- - and a chosen truth predicate `TruthK : Code → Set`.
--
-- The key structural discipline is decode-extensionality: properties only
-- depend on the decoded semantics, not on the concrete code representation.

DecodeExtensional
  : ∀ {ℓCode ℓDec ℓP : Level}
    {Code : Set ℓCode} {Dec : Set ℓDec}
    (decode : Code → Dec)
    (P : Code → Set ℓP)
  → Set (ℓCode ⊔ ℓDec ⊔ ℓP)
DecodeExtensional decode P =
  ∀ γ₁ γ₂ → decode γ₁ ≡ decode γ₂ → P γ₁ → P γ₂

record Admissible
  {ℓCode ℓDec ℓT ℓP : Level}
  (Code   : Set ℓCode)
  (Dec    : Set ℓDec)
  (decode : Code → Dec)
  (step   : Code → Code)
  (TruthK : Code → Set ℓT)
  (P      : Code → Set ℓP)
  : Set (ℓCode ⊔ ℓDec ⊔ ℓT ⊔ ℓP) where
  field
    ext    : DecodeExtensional decode P
    sound  : ∀ {γ} → P γ → TruthK γ
    stable : ∀ γ → P γ ↔ P (step γ)

open Admissible public

-- Non-vacuity guard for observer semantics: TruthK is neither trivial nor
-- entirely insensitive to decoding.

record NonVacuousObserver
  {ℓCode ℓDec ℓT : Level}
  (Code   : Set ℓCode)
  (Dec    : Set ℓDec)
  (decode : Code → Dec)
  (TruthK : Code → Set ℓT)
  : Set (ℓCode ⊔ ℓDec ⊔ ℓT) where
  field
    trueWitness  : Σ Code (λ γ → TruthK γ)
    falseWitness : Σ Code (λ γ → ¬ TruthK γ)
    decodeDistinct : Σ Code (λ γ₁ → Σ Code (λ γ₂ → ¬ (decode γ₁ ≡ decode γ₂)))

-- “Largest admissible predicate” (a la Comm⋆ / Obs⋆): P⋆ γ holds iff there
-- exists some admissible predicate P that contains γ.
--
-- Universe note: because `Pred⋆` is a `Σ` over predicates `P : Code → Set ℓP`,
-- the result lives one universe higher (in `… ⊔ lsuc ℓP`). This is intentional:
-- setting `ℓP = lsuc ℓ` allows witness-carrying observers (traces/certificates),
-- while setting `ℓP = ℓ` tightens types at the cost of restricting observers.

Pred⋆
  : ∀ {ℓCode ℓDec ℓT ℓP : Level}
    {Code : Set ℓCode} {Dec : Set ℓDec}
    (decode : Code → Dec)
    (step   : Code → Code)
    (TruthK : Code → Set ℓT)
  → Code → Set (ℓCode ⊔ ℓDec ⊔ ℓT ⊔ lsuc ℓP)
Pred⋆ {ℓP = ℓP} {Code} {Dec} decode step TruthK γ =
  Σ (Code → Set ℓP) (λ P → Admissible Code Dec decode step TruthK P × P γ)

-- --------------------------------------------------------------------------
-- Derived facts: Pred⋆ is the largest admissible predicate.
-- --------------------------------------------------------------------------

Pred⋆-contains
  : ∀ {ℓCode ℓDec ℓT ℓP : Level}
    {Code : Set ℓCode} {Dec : Set ℓDec}
    (decode : Code → Dec)
    (step   : Code → Code)
    (TruthK : Code → Set ℓT)
    (P      : Code → Set ℓP)
  → Admissible Code Dec decode step TruthK P
  → ∀ {γ} → P γ → Pred⋆ {ℓP = ℓP} decode step TruthK γ
Pred⋆-contains _ _ _ P AP p = P , (AP , p)

Pred⋆-sound
  : ∀ {ℓCode ℓDec ℓT ℓP : Level}
    {Code : Set ℓCode} {Dec : Set ℓDec}
    (decode : Code → Dec)
    (step   : Code → Code)
    (TruthK : Code → Set ℓT)
  → ∀ {γ} → Pred⋆ {ℓP = ℓP} decode step TruthK γ → TruthK γ
Pred⋆-sound _ _ _ (P , (AP , p)) = sound AP p

Pred⋆-ext
  : ∀ {ℓCode ℓDec ℓT ℓP : Level}
    {Code : Set ℓCode} {Dec : Set ℓDec}
    (decode : Code → Dec)
    (step   : Code → Code)
    (TruthK : Code → Set ℓT)
  → DecodeExtensional decode (Pred⋆ {ℓP = ℓP} decode step TruthK)
Pred⋆-ext decode step TruthK γ₁ γ₂ eq (P , (AP , p)) =
  P , (AP , ext AP γ₁ γ₂ eq p)

Pred⋆-stable
  : ∀ {ℓCode ℓDec ℓT ℓP : Level}
    {Code : Set ℓCode} {Dec : Set ℓDec}
    (decode : Code → Dec)
    (step   : Code → Code)
    (TruthK : Code → Set ℓT)
  → ∀ γ → Pred⋆ {ℓP = ℓP} decode step TruthK γ ↔ Pred⋆ {ℓP = ℓP} decode step TruthK (step γ)
Pred⋆-stable decode step TruthK γ =
  intro
    (λ (P , (AP , p)) → P , (AP , to (stable AP γ) p))
    (λ (P , (AP , p)) → P , (AP , from (stable AP γ) p))

Pred⋆-admissible
  : ∀ {ℓCode ℓDec ℓT ℓP : Level}
    {Code : Set ℓCode} {Dec : Set ℓDec}
    (decode : Code → Dec)
    (step   : Code → Code)
    (TruthK : Code → Set ℓT)
  → Admissible Code Dec decode step TruthK (Pred⋆ {ℓP = ℓP} decode step TruthK)
Pred⋆-admissible decode step TruthK =
  record
    { ext    = Pred⋆-ext decode step TruthK
    ; sound  = Pred⋆-sound decode step TruthK
    ; stable = Pred⋆-stable decode step TruthK
    }

Pred⋆-largest
  : ∀ {ℓCode ℓDec ℓT ℓP : Level}
    {Code : Set ℓCode} {Dec : Set ℓDec}
    (decode : Code → Dec)
    (step   : Code → Code)
    (TruthK : Code → Set ℓT)
    (P      : Code → Set ℓP)
  → Admissible Code Dec decode step TruthK P
  → ∀ γ → P γ → Pred⋆ {ℓP = ℓP} decode step TruthK γ
Pred⋆-largest decode step TruthK P AP γ p =
  Pred⋆-contains decode step TruthK P AP p

-- Safe reflection aliases (generic, semantically polymorphic in TruthK).
-- In the reflection literature, "soundness" is the reflection principle
-- (safe predicates imply truth), and "stability" is the modal safety guard.

SafeAdmissible = Admissible

Safe⋆ = Pred⋆

safe⋆-sound = Pred⋆-sound
safe⋆-ext = Pred⋆-ext
safe⋆-stable = Pred⋆-stable
safe⋆-admissible = Pred⋆-admissible
safe⋆-largest = Pred⋆-largest
