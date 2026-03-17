{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.AsymptoticReification.SuccessorBridge where

-- Canonical successor-step bridge over a fixed lower rung and upper carrier.
--
-- This packages the two pieces that previously traveled separately:
-- - cross-stage predicate reification,
-- - the induced cross-stage FO witnesses.

open import LogOS.Prelude
open import LogOS.LT.View using (μ)
open import LogOS.Syntax.Prop using (_↔_)

import LogOS.Apps.ZFC.Stack.AsymptoticReification.CrossStageFOFromReification as CSFO
import LogOS.Apps.ZFC.Stack.AsymptoticReification.CrossStageReificationPort as CSR
import LogOS.Apps.ZFC.Proof.Syntax as Syn
import LogOS.Apps.ZFC.Stack.ProfileTower.Core as Tower
import LogOS.Apps.ZFC.Stack.ZFCore as ZF

record SuccessorBridge
  {ℓ₀ ℓ₁ : Level}
  (B : Tower.ZFStackBase {ℓ₀})
  (C₁ : ZF.SetContext {ℓ₁})
  : Set (lsuc (lsuc (ℓ₀ ⊔ ℓ₁))) where

  field
    reification : CSR.CrossStagePredicateReification (Tower.ZFStackBase.ctx B) C₁

  module Cross = CSFO.CrossStageFO B C₁ reification

  field
    foWitnesses : Cross.CrossStageFOWitnesses

  module U₀ = Tower.ZFStackBase B
  module U₁ = ZF.SetContext C₁
  module FB = Cross.FB
  module R = Cross.R

  open Cross public using
    ( SepPred
    ; RepPred
    ; CrossStageFOWitnesses
    )

  SeparationFV↑ = Cross.SeparationFV↑ foWitnesses
  ReplacementFV↑ = Cross.ReplacementFV↑ foWitnesses
  separation-spec↑ = Cross.separation-spec↑ foWitnesses
  replacement-spec↑ = Cross.replacement-spec↑ foWitnesses

  separationSet↑ : (P : Syn.Formula) → FB.Valuation → U₀.SetU → U₁.SetU
  separationSet↑ P ρ x = μ (SeparationFV↑ P ρ) x

  replacementSet↑
    : (R₀ : Syn.Formula)
    → (ρ : FB.Valuation)
    → Σ U₀.SetU (λ x → FB.FunctionalOnX R₀ ρ x)
    → U₁.SetU
  replacementSet↑ R₀ ρ xf = μ (ReplacementFV↑ R₀ ρ) xf

  separation-schema↑
    : ∀ (P : Syn.Formula) (ρ : FB.Valuation) (x z : U₀.SetU)
    → U₁._∈_ (R.embed z) (separationSet↑ P ρ x) ↔ SepPred P ρ x z
  separation-schema↑ = separation-spec↑

  replacement-schema↑
    : ∀ (R₀ : Syn.Formula) (ρ : FB.Valuation)
    → ∀ (x : U₀.SetU)
    → (fun : FB.FunctionalOnX R₀ ρ x)
    → ∀ z
    → U₁._∈_ (R.embed z) (replacementSet↑ R₀ ρ (x , fun))
        ↔ RepPred R₀ ρ x z
  replacement-schema↑ = replacement-spec↑

open SuccessorBridge public
