{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.MembershipLocality where

-- Membership locality: the canonical distributed semantics of sets.
--
-- Idea:
-- - take the locality index as potential members `z : SetU`,
-- - take the local observable at `z` to be the truth value of `z ∈ x`,
-- - the resulting dependent boundary is a predicate space `SetU → Set ℓ`.
--
-- In this reading, the set boundary preorder is not primitive: it is the
-- pullback refinement induced by the membership observation map. This matches
-- the LogOS stance “relations are introduced as pullbacks of explicit views”.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; _⊑_)
open import LogOS.LT.Flow using (idClosure)
open import LogOS.LT.View using (View; μ)
open import LogOS.LT.Presentation.ObservationInitiality using (SuiteForcedᵈ)
open import LogOS.Ports.PhysicalSemantics.Core using (DependentLocalSemantics)
open import LogOS.Ports.Locality.Core using (LocalityPort; localView; suite)

open import LogOS.Apps.ZFC.Stack.Boundary using
  ( MembershipObs
  ; PredicateBoundary
  ; membershipView
  ; SetBoundary
  )

import LogOS.Apps.ZFC.Stack.ZFCore as ZF

module ForContext {ℓ : Level} (C : ZF.SetContext {ℓ}) where
  open ZF.SetContext C using (SetU; _∈_)

  -- Local observation preorder (truth values, ordered by reverse implication).
  Obs : ConPreorder (lsuc ℓ) ℓ
  Obs = MembershipObs {ℓ}

  -- Dependent boundary of predicates over `SetU` (reverse pointwise implication).
  PredBnd : ConPreorder (lsuc ℓ) ℓ
  PredBnd = PredicateBoundary SetU

  -- View into the predicate boundary: `x ↦ (z ↦ z ∈ x)`.
  memV : View SetU PredBnd
  memV = membershipView SetU _∈_

  -- The induced set boundary preorder (reverse inclusion).
  SetBnd : ConPreorder ℓ ℓ
  SetBnd = SetBoundary SetU _∈_

  -- A `DependentLocalSemantics` ledger whose dependent boundary is `PredBnd`.
  --
  -- Note: `DependentLocalSemantics` does not constrain the carrier levels of `I` and
  -- `O i` to be equal; downstream facades may still choose same-level
  -- specialisations.
  Sem : DependentLocalSemantics {ℓI = ℓ} {ℓOCon = lsuc ℓ} {ℓORel = ℓ}
  Sem =
    record
      { I = SetU
      ; O = λ _ → Obs
      ; GC₀ = λ _ → idClosure Obs
      }

  -- Sets themselves as a dependent locality port (one probe per potential member).
  setsPort : LocalityPort SetU SetU (λ _ → Obs)
  setsPort =
    record
      { localProbe = λ z → record { μ = λ x → z ∈ x } }

  -- Sanity check: the combined observation is definitionally membership.
  memV-μ : ∀ x z → μ (localView setsPort) x z ≡ (z ∈ x)
  memV-μ _ _ = refl

  -- Observation-initiality reading:
  -- any relation on sets that is monotone w.r.t. every membership probe is
  -- contained in the induced set refinement.
  membership-forces-refinement
    : ∀ {ℓR : Level}
      (≼ : SetU → SetU → Set ℓR)
    → (∀ {x y} → ≼ x y → ∀ z → z ∈ y → z ∈ x)
    → ∀ {x y} → ≼ x y → _⊑_ SetBnd x y
  membership-forces-refinement ≼ hyp le =
    SuiteForcedᵈ (suite setsPort) ≼ (λ le' z → hyp le' z) le
