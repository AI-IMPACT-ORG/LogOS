{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.AsymptoticReification.CrossStageFOFromReification where

open import LogOS.Prelude
open import LogOS.LT.View using (View; μ)
open import LogOS.Syntax.Prop using (_↔_)

import LogOS.Apps.ZFC.Stack.ProfileTower.Core as Tower
import LogOS.Apps.ZFC.Stack.ProfileTowerFO as TowerFO
import LogOS.Apps.ZFC.Stack.ZFCore as ZF
import LogOS.Apps.ZFC.Proof.Syntax as Syn

open import LogOS.Apps.ZFC.Stack.AsymptoticReification.CrossStageReificationPort using
  ( CrossStagePredicateReification )

module CrossStageFO
  {ℓ₀ ℓ₁ : Level}
  (B : Tower.ZFStackBase {ℓ₀})
  (C₁ : ZF.SetContext {ℓ₁})
  (R↑ : CrossStagePredicateReification (Tower.ZFStackBase.ctx B) C₁)
  where

  open Tower.ZFStackBase B
  module R = CrossStagePredicateReification R↑
  open ZF.SetContext C₁ renaming
    ( SetU to SetU↑
    ; _∈_ to _∈↑_
    ; SetBnd to SetBnd↑
    )
  module FB = TowerFO.ForBase B

  SepPred : Syn.Formula → FB.Valuation → SetU → R.Predicate₀
  SepPred P ρ x z = (z ∈ x) × FB.evalFormula P (FB.extend z (FB.extend x ρ))

  RepPred : Syn.Formula → FB.Valuation → SetU → R.Predicate₀
  RepPred R₀ ρ x z =
    Σ SetU (λ u → u ∈ x × FB.evalFormula R₀ (FB.extend u (FB.extend z ρ)))

  record CrossStageFOWitnesses : Set (lsuc (ℓ₀ ⊔ ℓ₁)) where
    field
      sepReifiable
        : ∀ (P : Syn.Formula) (ρ : FB.Valuation) (x : SetU)
        → R.Reifiable (SepPred P ρ x)

      repReifiable
        : ∀ (R₀ : Syn.Formula) (ρ : FB.Valuation) (x : SetU)
        → FB.FunctionalOnX R₀ ρ x
        → R.Reifiable (RepPred R₀ ρ x)

  SeparationFV↑
    : CrossStageFOWitnesses
    → (P : Syn.Formula)
    → (ρ : FB.Valuation)
    → View SetU SetBnd↑
  SeparationFV↑ W P ρ =
    record { μ = λ x → R.reify (SepPred P ρ x) (CrossStageFOWitnesses.sepReifiable W P ρ x) }

  separation-spec↑
    : (W : CrossStageFOWitnesses)
    → ∀ (P : Syn.Formula) (ρ : FB.Valuation) (x z : SetU)
    → (R.embed z ∈↑ μ (SeparationFV↑ W P ρ) x)
        ↔ ((z ∈ x) × FB.evalFormula P (FB.extend z (FB.extend x ρ)))
  separation-spec↑ W P ρ x z =
    R.mem-reify↔
      (SepPred P ρ x)
      (CrossStageFOWitnesses.sepReifiable W P ρ x)
      z

  ReplacementFV↑
    : CrossStageFOWitnesses
    → (R₀ : Syn.Formula)
    → (ρ : FB.Valuation)
    → View (Σ SetU (λ x → FB.FunctionalOnX R₀ ρ x)) SetBnd↑
  ReplacementFV↑ W R₀ ρ =
    record
      { μ = λ (x , fun) → R.reify (RepPred R₀ ρ x) (CrossStageFOWitnesses.repReifiable W R₀ ρ x fun) }

  replacement-spec↑
    : (W : CrossStageFOWitnesses)
    → ∀ (R₀ : Syn.Formula) (ρ : FB.Valuation)
    → ∀ (x : SetU)
    → (fun : FB.FunctionalOnX R₀ ρ x)
    → ∀ z
    → (R.embed z ∈↑ μ (ReplacementFV↑ W R₀ ρ) (x , fun))
        ↔ (Σ SetU (λ u → u ∈ x × FB.evalFormula R₀ (FB.extend u (FB.extend z ρ))))
  replacement-spec↑ W R₀ ρ x fun z =
    R.mem-reify↔
      (RepPred R₀ ρ x)
      (CrossStageFOWitnesses.repReifiable W R₀ ρ x fun)
      z
