{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.AsymptoticReification.ReificationPort where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; intro)
open import LogOS.LT.Flow using (GuardedClosure; Flow; infl)
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_)
open import LogOS.LT.View using (View; μ)

import LogOS.Ports.Reification.Admissible as Core

open import LogOS.Apps.ZFC.Stack.Boundary using (PredicateBoundary; membershipView)
import LogOS.Apps.ZFC.Stack.ZFCore as ZF

-- ------------------------------------------------------------------------
-- Reification port on the membership-local predicate boundary.
--
-- This port is intentionally *restricted-by-default*:
-- `reify` is gated by an explicit admissibility witness `Reifiable P`.
--
-- Rationale:
-- unrestricted (total) reification on the full predicate boundary, especially
-- under `idClosure`, enables Russell-style diagonal predicates.

record PredicateReification {ℓ : Level} (C : ZF.SetContext {ℓ}) : Set (lsuc (lsuc ℓ)) where
  open ZF.SetContext C using (SetU; _∈_; _≈_)

  -- Predicate boundary: membership observables, one probe per potential member.
  PredBnd : ConPreorder (lsuc ℓ) ℓ
  PredBnd = PredicateBoundary SetU

  Predicate : Set (lsuc ℓ)
  Predicate = Con PredBnd

  -- Canonical constructor predicates (shape only; no stability assumed).
  EmptyPred : Predicate
  EmptyPred _ = ⊥

  PairPred : SetU → SetU → Predicate
  PairPred x y z = (z ≈ x) ⊎ (z ≈ y)

  UnionPred : SetU → Predicate
  UnionPred x z = Σ SetU (λ y → (y ∈ x) × (z ∈ y))

  PowersetPred : SetU → Predicate
  PowersetPred x z = ∀ w → w ∈ z → w ∈ x

  field
    GC : GuardedClosure PredBnd

    -- Declared admissibility family: which predicates may be reified as sets.
    Reifiable : Predicate → Set (lsuc ℓ)

    -- Reification into the set carrier:
    -- turn an admissible predicate into a set whose membership predicate matches `Flow`.
    reify : (P : Predicate) → Reifiable P → SetU

    mem-reify↔
      : ∀ (P : Predicate) (rP : Reifiable P) (z : SetU)
      → (z ∈ reify P rP) ↔ (Flow GC P z)

    -- Core admissibility witnesses (so downstream modules do not need to re-declare them).
    emptyReifiable : Reifiable EmptyPred
    pairReifiable : ∀ x y → Reifiable (PairPred x y)
    unionReifiable : ∀ x → Reifiable (UnionPred x)
    powersetReifiable : ∀ x → Reifiable (PowersetPred x)

  -- Membership observation as a view into the predicate boundary.
  obs : View SetU PredBnd
  obs = membershipView SetU _∈_

  -- Core restricted reification interface induced by the pointwise law.
  core : Core.RestrictedReification obs
  core =
    record
      { GC = GC
      ; Reifiable = Reifiable
      ; reify = reify
      ; decode-reify≈Flow =
          λ P rP →
            ( (λ z → _↔_.from (mem-reify↔ P rP z))
            , (λ z → _↔_.to   (mem-reify↔ P rP z))
            )
      }

-- ------------------------------------------------------------------------
-- Total/unrestricted reification (explicitly strong; intended for experiments).
--
-- This record matches the historical `PredicateReification` surface (ungated `reify`).
record TotalPredicateReification {ℓ : Level} (C : ZF.SetContext {ℓ}) : Set (lsuc (lsuc ℓ)) where
  open ZF.SetContext C using (SetU; _∈_)

  PredBnd : ConPreorder (lsuc ℓ) ℓ
  PredBnd = PredicateBoundary SetU

  Predicate : Set (lsuc ℓ)
  Predicate = Con PredBnd

  field
    GC : GuardedClosure PredBnd

    reify : Predicate → SetU

    mem-reify↔
      : ∀ (P : Predicate) (z : SetU)
      → (z ∈ reify P) ↔ (Flow GC P z)

  obs : View SetU PredBnd
  obs = membershipView SetU _∈_

  core : Core.TotalReification obs
  core =
    record
      { GC = GC
      ; reify = reify
      ; decode-reify≈Flow =
          λ P →
            ( (λ z → _↔_.from (mem-reify↔ P z))
            , (λ z → _↔_.to   (mem-reify↔ P z))
            )
      }

-- Convert total/unrestricted reification to the restricted port by declaring
-- every predicate admissible (`Reifiable = ⊤`).
total→restricted
  : ∀ {ℓ : Level} {C : ZF.SetContext {ℓ}}
  → TotalPredicateReification C
  → PredicateReification C
total→restricted {C = C} T =
  record
    { GC = TotalPredicateReification.GC T
    ; Reifiable = λ _ → ⊤
    ; reify = λ P _ → TotalPredicateReification.reify T P
    ; mem-reify↔ = λ P _ z → TotalPredicateReification.mem-reify↔ T P z
    ; emptyReifiable = tt
    ; pairReifiable = λ _ _ → tt
    ; unionReifiable = λ _ → tt
    ; powersetReifiable = λ _ → tt
    }

-- Convert restricted reification to total reification, given a proof that all
-- predicates are admissible.
restricted→total
  : ∀ {ℓ : Level} {C : ZF.SetContext {ℓ}}
  → (R : PredicateReification C)
  → (total : ∀ P → PredicateReification.Reifiable R P)
  → TotalPredicateReification C
restricted→total {C = C} R total =
  record
    { GC = PredicateReification.GC R
    ; reify = λ P → PredicateReification.reify R P (total P)
    ; mem-reify↔ = λ P z → PredicateReification.mem-reify↔ R P (total P) z
    }

-- If a predicate is already stable w.r.t. `Flow`, then `Flow P` is pointwise
-- equivalent to `P`. This is the “already at the asymptote” criterion.
--
-- Note: on the predicate boundary, refinement is reverse implication, so
-- `Flow P ⊑ P` reads as “P implies Flow P” pointwise.
stablePredicate↔
  : ∀ {ℓ : Level} {C : ZF.SetContext {ℓ}}
  → (R : PredicateReification C)
  → (P : PredicateReification.Predicate R)
  → _⊑_ (PredicateReification.PredBnd R)
      (Flow (PredicateReification.GC R) P)
      P
  → (z : ZF.SetContext.SetU C)
  → P z ↔ Flow (PredicateReification.GC R) P z
stablePredicate↔ {C = C} R P stableP z =
  intro
    (stableP z)
    (infl (PredicateReification.GC R) P z)

-- Reifying a stable predicate yields exact membership behaviour (no extra `Flow`
-- visible at the proposition level).
mem-reify-stable↔
  : ∀ {ℓ : Level} {C : ZF.SetContext {ℓ}}
  → (R : PredicateReification C)
  → (P : PredicateReification.Predicate R)
  → (rP : PredicateReification.Reifiable R P)
  → _⊑_ (PredicateReification.PredBnd R)
      (Flow (PredicateReification.GC R) P)
      P
  → ∀ z
  → (ZF.SetContext._∈_ C z (PredicateReification.reify R P rP)) ↔ P z
mem-reify-stable↔ {C = C} R P rP stableP z =
  let
    open PredicateReification R
    reify≈P = Core.decode-reify-stable≈ core P rP stableP

    -- On the predicate boundary, `≈` is pointwise `↔` (reverse-implication polarity).
    pointwise↔ : (μ obs (reify P rP) z) ↔ P z
    pointwise↔ = intro (snd reify≈P z) (fst reify≈P z)
  in
  pointwise↔
