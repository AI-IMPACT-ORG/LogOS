{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.AsymptoticReification.GuardedLawvere where

-- Predicate reification specialised to the guarded-Lawvere schema.
--
-- Design note:
-- total predicate reification names `Flow`-normalised predicates. To recover
-- exact point-surjectivity for all predicates, this module takes an explicit
-- `FlowCollapse` witness.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; intro; ↔-sym; ↔-trans)
open import LogOS.LT.ConPreorder using (_⊑_; _≈_)
open import LogOS.LT.ConPreorder.Truth using (TruthPreorder)
open import LogOS.LT.Flow using (GuardedClosure; Flow; Stable; mkStable; elem; idClosure)
open import LogOS.Ports.Reification.GuardedLawvere using
  ( StableEvaluator
  ; QuotedPointSurjective
  ; noStableFixedPoint-obstructsQuotedPointSurjective
  )

import LogOS.Apps.ZFC.Stack.ZFCore as ZF
open import LogOS.Apps.ZFC.Stack.AsymptoticReification.ReificationPort using
  ( TotalPredicateReification
  )

module For {ℓ : Level} (C : ZF.SetContext {ℓ}) where
  open ZF.SetContext C using (SetU; _∈_)

  TruthGC = idClosure (TruthPreorder {ℓ})

  membershipEvaluator : StableEvaluator SetU SetU (TruthPreorder {ℓ}) TruthGC
  membershipEvaluator =
    record
      { eval = λ a x → mkStable (x ∈ a) (λ px → px) }

  FlowCollapse
    : TotalPredicateReification C
    → Set (lsuc ℓ)
  FlowCollapse R =
    ∀ P → _⊑_ (TotalPredicateReification.PredBnd R)
            (Flow (TotalPredicateReification.GC R) P)
            P

  flowCollapse↔
    : ∀ (R : TotalPredicateReification C)
    → FlowCollapse R
    → (P : TotalPredicateReification.Predicate R)
    → (z : SetU)
    → P z ↔ Flow (TotalPredicateReification.GC R) P z
  flowCollapse↔ R collapse P z =
    intro
      (collapse P z)
      (GuardedClosure.infl (TotalPredicateReification.GC R) P z)

  totalPredicateReification→QuotedPointSurjective
    : (R : TotalPredicateReification C)
    → FlowCollapse R
    → QuotedPointSurjective membershipEvaluator
  totalPredicateReification→QuotedPointSurjective R collapse =
    record
      { quotePoint = λ x → x
      ; namesEvery = λ φ →
          let
            P : TotalPredicateReification.Predicate R
            P z = elem (φ z)

            a : SetU
            a = TotalPredicateReification.reify R P

            pointwise
              : ∀ z → _≈_ (TruthPreorder {ℓ}) (elem (StableEvaluator.eval membershipEvaluator a z)) (elem (φ z))
            pointwise z =
              let
                reify↔ = TotalPredicateReification.mem-reify↔ R P z
                collapse↔ = flowCollapse↔ R collapse P z
                exact↔ = ↔-trans reify↔ (↔-sym collapse↔)
              in
              (_↔_.to exact↔ , _↔_.from exact↔)
          in
          a , pointwise
      }

  diagonalNoFixedPoint-obstructsTotalPredicateReification
    : (diag : Σ
        (Stable {CP = TruthPreorder {ℓ}} (Flow TruthGC)
          → Stable {CP = TruthPreorder {ℓ}} (Flow TruthGC))
        (λ α → ∀ p
          → ¬ _≈_ (TruthPreorder {ℓ}) (elem p) (elem (α p))))
    → (R : TotalPredicateReification C)
    → FlowCollapse R
    → ⊥
  diagonalNoFixedPoint-obstructsTotalPredicateReification diag R collapse =
    noStableFixedPoint-obstructsQuotedPointSurjective
      diag
      (totalPredicateReification→QuotedPointSurjective R collapse)
