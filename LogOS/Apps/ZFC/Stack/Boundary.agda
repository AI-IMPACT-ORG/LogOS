{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.Boundary where

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder)
open import LogOS.LT.ConPreorder.Truth using (TruthBoundary)
open import LogOS.LT.View using (View; μ)
open import LogOS.Ports.Locality.Core using
  ( LocalBoundary
  ; LocalityPort
  ; localView
  ; LocalityPreorder
  )

-- The canonical boundary preorder induced by a membership relation.
-- Interpret each `x : SetU` as the predicate `z ↦ (z ∈ x)`.
--
-- Refinement follows the LogOS convention: `x ⊑ y` means “y entails x”,
-- i.e. every member of `y` is also a member of `x` (reverse inclusion).

-- Boundary of truth values for membership probes (reverse implication).
MembershipObs : ∀ {ℓ : Level} → ConPreorder (lsuc ℓ) ℓ
MembershipObs {ℓ} = TruthBoundary {ℓ}

-- Boundary of membership predicates on `SetU` (reverse pointwise implication).
PredicateBoundary : ∀ {ℓ : Level} → (SetU : Set ℓ) → ConPreorder (lsuc ℓ) ℓ
PredicateBoundary {ℓ} SetU = LocalBoundary SetU (λ _ → MembershipObs {ℓ})

-- Membership probes as a dependent locality port (one probe per potential member).
membershipPort
  : ∀ {ℓ : Level}
  → (SetU : Set ℓ)
  → (_∈_ : SetU → SetU → Set ℓ)
  → LocalityPort SetU SetU (λ _ → MembershipObs {ℓ})
membershipPort _ _∈_ =
  record
    { localProbe = λ z → record { μ = λ x → z ∈ x } }

-- Observation map: a set denotes its membership predicate `z ↦ (z ∈ x)`.
membershipView
  : ∀ {ℓ : Level}
  → (SetU : Set ℓ)
  → (_∈_ : SetU → SetU → Set ℓ)
  → View SetU (PredicateBoundary SetU)
membershipView SetU _∈_ = localView (membershipPort SetU _∈_)

SetBoundary
  : ∀ {ℓ : Level}
  → (SetU : Set ℓ)
  → (_∈_ : SetU → SetU → Set ℓ)
  → ConPreorder ℓ ℓ
SetBoundary SetU _∈_ = LocalityPreorder (membershipPort SetU _∈_)
