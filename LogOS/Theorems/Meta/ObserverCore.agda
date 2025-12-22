{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.ObserverCore where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)
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

-- “Largest admissible predicate” (a la Comm⋆ / Obs⋆): P⋆ γ holds iff there
-- exists some admissible predicate P that contains γ.

Pred⋆
  : ∀ {ℓCode ℓDec ℓT ℓP : Level}
    {Code : Set ℓCode} {Dec : Set ℓDec}
    (decode : Code → Dec)
    (step   : Code → Code)
    (TruthK : Code → Set ℓT)
  → Code → Set (ℓCode ⊔ ℓDec ⊔ ℓT ⊔ lsuc ℓP)
Pred⋆ {ℓP = ℓP} {Code} {Dec} decode step TruthK γ =
  Σ (Code → Set ℓP) (λ P → Admissible Code Dec decode step TruthK P × P γ)
