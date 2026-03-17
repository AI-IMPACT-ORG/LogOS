{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.AsymptoticReification.CoreFromReification where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)
open import LogOS.LT.Flow using (Flow)
open import LogOS.LT.ConPreorder using (_⊑_)
open import LogOS.LT.View using (View; μ)

import LogOS.Apps.ZFC.Stack.ZFCore as ZF
import LogOS.Apps.ZFC.Stack.ProfileTower.Core as Tower

open import LogOS.Apps.ZFC.Stack.AsymptoticReification.ReificationPort using
  ( PredicateReification
  ; mem-reify-stable↔
  )

-- ------------------------------------------------------------------------
-- Core ZF constructors from reification (Empty/Pair/Union/Powerset).
--
-- This is the "collapse only at the boundary" move:
-- the constructor Views are defined by reifying their intended membership
-- predicates, and the corresponding membership laws become available exactly
-- when those predicates are stable w.r.t. the chosen `Flow`.

module Core {ℓ : Level} (C : ZF.SetContext {ℓ}) (R : PredicateReification C) where
  open ZF.SetContext C
  open PredicateReification R

  FlowCollapse : Set (lsuc ℓ)
  FlowCollapse = ∀ P → _⊑_ PredBnd (Flow GC P) P

  -- Stability obligations (“already at the asymptote”).
  --
  -- We separate these from the reification port so consumers can:
  -- - keep `Flow` nontrivial, and
  -- - explicitly list exactly which predicates they assume stable.
  record CoreStability : Set (lsuc (lsuc ℓ)) where
    field
      pairStable
        : ∀ x y → _⊑_ PredBnd (Flow GC (PairPred x y)) (PairPred x y)

      unionStable
        : ∀ x → _⊑_ PredBnd (Flow GC (UnionPred x)) (UnionPred x)

      powersetStable
        : ∀ x → _⊑_ PredBnd (Flow GC (PowersetPred x)) (PowersetPred x)

  coreStabilityFromFlowCollapse
    : FlowCollapse
    → CoreStability
  coreStabilityFromFlowCollapse close =
    record
      { pairStable = λ x y → close (PairPred x y)
      ; unionStable = λ x → close (UnionPred x)
      ; powersetStable = λ x → close (PowersetPred x)
      }

  -- Empty predicate stability holds because EmptyPred entails everything.
  emptyStable : _⊑_ PredBnd (Flow GC EmptyPred) EmptyPred
  emptyStable z ()

  -- Reified constructor Views into the set boundary.

  EmptyVᵣ : View (⊤ {ℓ}) SetBnd
  EmptyVᵣ = record { μ = λ _ → reify EmptyPred emptyReifiable }

  PairVᵣ : View (SetU × SetU) SetBnd
  PairVᵣ =
    record
      { μ = λ { (x , y) → reify (PairPred x y) (pairReifiable x y) } }

  UnionVᵣ : View SetU SetBnd
  UnionVᵣ = record { μ = λ x → reify (UnionPred x) (unionReifiable x) }

  PowersetVᵣ : View SetU SetBnd
  PowersetVᵣ = record { μ = λ x → reify (PowersetPred x) (powersetReifiable x) }

  -- Membership laws for the reified constructors.

  empty-specᵣ
    : ∀ z → ¬ (z ∈ μ EmptyVᵣ tt)
  empty-specᵣ z z∈ =
    ⊥-elim (_↔_.to (mem-reify-stable↔ R EmptyPred emptyReifiable emptyStable z) z∈)

  pairing-specᵣ
    : (stab : CoreStability)
    → ∀ x y z
    → (z ∈ μ PairVᵣ (x , y)) ↔ ((z ≈ x) ⊎ (z ≈ y))
  pairing-specᵣ stab x y z =
    mem-reify-stable↔
      R
      (PairPred x y)
      (pairReifiable x y)
      (CoreStability.pairStable stab x y)
      z

  union-specᵣ
    : (stab : CoreStability)
    → ∀ x z
    → (z ∈ μ UnionVᵣ x) ↔ (Σ SetU (λ y → (y ∈ x) × (z ∈ y)))
  union-specᵣ stab x z =
    mem-reify-stable↔
      R
      (UnionPred x)
      (unionReifiable x)
      (CoreStability.unionStable stab x)
      z

  powerset-specᵣ
    : (stab : CoreStability)
    → ∀ x z
    → (z ∈ μ PowersetVᵣ x) ↔ (∀ w → w ∈ z → w ∈ x)
  powerset-specᵣ stab x z =
    mem-reify-stable↔
      R
      (PowersetPred x)
      (powersetReifiable x)
      (CoreStability.powersetStable stab x)
      z

  -- Package the reified constructors as ZF signature profiles.

  coreSigᵣ : ZF.ZFSignatureCore C
  coreSigᵣ =
    record
      { EmptyV = EmptyVᵣ
      ; PairV = PairVᵣ
      ; UnionV = UnionVᵣ
      }

  coreLawsᵣ
    : (stab : CoreStability)
    → ZF.ZFLawsCore C coreSigᵣ
  coreLawsᵣ stab =
    record
      { empty-spec = empty-specᵣ
      ; pairing-spec = pairing-specᵣ stab
      ; union-spec = union-specᵣ stab
      }

  powSigᵣ : ZF.ZFSignaturePowerset C
  powSigᵣ = record { PowersetV = PowersetVᵣ }

  powersetLawsᵣ
    : (stab : CoreStability)
    → ZF.ZFLawsPowerset C powSigᵣ
  powersetLawsᵣ stab =
    record
      { powerset-spec = powerset-specᵣ stab }

  -- Package the reified core + powerset profiles as a `ZFStackBase` once ω
  -- and Infinity are supplied as additional explicit assumptions.
  --
  -- This is a *constructor path*, not a derivation: the extra laws are
  -- parameters so downstream users can audit exactly what is assumed beyond
  -- the reification doctrine.
  zfStackBaseFromReification
    : (stab : CoreStability)
    → (ωSig : ZF.ZFSignatureOmega C)
    → ZF.ZFLawsInfinity C coreSigᵣ ωSig
    → Tower.ZFStackBase {ℓ}
  zfStackBaseFromReification stab ωSig inf =
    record
      { ctx = C
      ; coreSig = coreSigᵣ
      ; powSig = powSigᵣ
      ; omegaSig = ωSig
      ; coreLaws = coreLawsᵣ stab
      ; powersetLaws = powersetLawsᵣ stab
      ; infinityLaws = inf
      }
