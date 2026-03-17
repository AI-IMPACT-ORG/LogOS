{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Models.IterativeSetTree.HierarchyInfinity where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; intro)
open import LogOS.LT.View using (μ)

import LogOS.Apps.ZFC.Stack.AsymptoticReification as AR
import LogOS.Apps.ZFC.Stack.ZFCore as ZF

import LogOS.Apps.ZFC.Models.IterativeSetTree as IST
import LogOS.Apps.ZFC.Models.IterativeSetTree.StageSetup as Setup
import LogOS.Apps.ZFC.Models.IterativeSetTree.StagedReification as Stage

module For {ℓ : Level} (H : Stage.StageAssumptionsᵛ {ℓ}) where
  module Setupᵛ = Setup.For H
  open Setupᵛ using (C; collapse; restrictedPredicateReificationᵛ; collapseFlowᵛ)
  module LC = Setupᵛ.LC
  open Stage.ExtensionalCollapseᵛ collapse using (extensionalityᵛ)
  module Core = AR.Core C restrictedPredicateReificationᵛ
  open ZF.SetContext C using (SetU; _∈_; _≈_; refl≈; sym≈; trans≈; ≡→≈)

  coreStability : Core.CoreStability
  coreStability = Core.coreStabilityFromFlowCollapse collapseFlowᵛ

  coreLaws : ZF.ZFLawsCore C Core.coreSigᵣ
  coreLaws = Core.coreLawsᵣ coreStability

  module D = ZF.DerivedCore Core.coreSigᵣ

  zeroSet : SetU
  zeroSet = μ D.ZeroV tt

  succSet : SetU → SetU
  succSet x = μ D.SuccV x

  succSet-spec : ∀ x z → (z ∈ succSet x) ↔ ((z ∈ x) ⊎ (z ≈ x))
  succSet-spec = ZF.succ-spec-from-core Core.coreSigᵣ coreLaws

  succᵛ-spec : ∀ x z → (z ∈ IST.succᵛ x) ↔ ((z ∈ x) ⊎ (z ≈ x))
  succᵛ-spec (IST.sup I f) z =
    intro to from
    where
      to : z IST.∈ᵛ IST.succᵛ (IST.sup I f) → (z IST.∈ᵛ IST.sup I f) ⊎ (z ≈ IST.sup I f)
      to (inj₁ ttℓ , refl) = inj₂ (refl≈ (IST.sup I f))
      to (inj₂ i , eq) = inj₁ (i , eq)

      from : (z IST.∈ᵛ IST.sup I f) ⊎ (z ≈ IST.sup I f) → z IST.∈ᵛ IST.succᵛ (IST.sup I f)
      from (inj₁ (i , eq)) = inj₂ i , eq
      from (inj₂ z≈x) = inj₁ ttℓ , extensionalityᵛ z≈x

  succᵛ≈succSet : ∀ x → IST.succᵛ x ≈ succSet x
  succᵛ≈succSet x = to , from
    where
      to : ∀ z → z ∈ IST.succᵛ x → z ∈ succSet x
      to z z∈ = _↔_.from (succSet-spec x z) (_↔_.to (succᵛ-spec x z) z∈)

      from : ∀ z → z ∈ succSet x → z ∈ IST.succᵛ x
      from z z∈ = _↔_.from (succᵛ-spec x z) (_↔_.to (succSet-spec x z) z∈)

  omegaSet : SetU
  omegaSet = IST.omegaᵛ

  zero∈omega : zeroSet ∈ omegaSet
  zero∈omega = IST.zero , refl

  infinity-specᵛ
    : ∀ z
    → (z ∈ omegaSet)
        ↔ ((z ≈ zeroSet)
          ⊎ (Σ SetU (λ y → y ∈ omegaSet × (z ≈ succSet y))))
  infinity-specᵛ z =
    intro to from
    where
      to
        : z ∈ omegaSet
        → (z ≈ zeroSet) ⊎ (Σ SetU (λ y → y ∈ omegaSet × (z ≈ succSet y)))
      to (IST.zero , eq) = inj₁ (≡→≈ eq)
      to (IST.sucℓ n , eq) =
        let
          y : SetU
          y = IST.vnNatᵛ n

          y∈ω : y ∈ omegaSet
          y∈ω = n , refl

          z≈succᵛy : z ≈ IST.succᵛ y
          z≈succᵛy = ≡→≈ eq

          z≈succy : z ≈ succSet y
          z≈succy = trans≈ z≈succᵛy (succᵛ≈succSet y)
        in
        inj₂ (y , (y∈ω , z≈succy))

      from
        : ((z ≈ zeroSet) ⊎ (Σ SetU (λ y → y ∈ omegaSet × (z ≈ succSet y))))
        → z ∈ omegaSet
      from (inj₁ z≈0) =
        subst (λ t → t ∈ omegaSet) (sym (extensionalityᵛ z≈0)) zero∈omega
      from (inj₂ (y , (y∈ω , z≈su))) with IST.memberOut y∈ω
      ... | (n , y≡n) =
        let
          z≈succᵛy : z ≈ IST.succᵛ y
          z≈succᵛy = trans≈ z≈su (sym≈ (succᵛ≈succSet y))

          z≡succᵛy : z ≡ IST.succᵛ y
          z≡succᵛy = extensionalityᵛ z≈succᵛy

          z≡succn : z ≡ IST.vnNatᵛ (IST.sucℓ n)
          z≡succn = trans z≡succᵛy (cong IST.succᵛ y≡n)
        in
        IST.sucℓ n , z≡succn

  omegaSigᵛ : ZF.ZFSignatureOmega C
  omegaSigᵛ = record { OmegaV = record { μ = λ _ → omegaSet } }

  infinityLawsᵛ : ZF.ZFLawsInfinity C Core.coreSigᵣ omegaSigᵛ
  infinityLawsᵛ = record { infinity-spec = infinity-specᵛ }

  baseAssumptions : LC.BaseAssumptions
  baseAssumptions =
    record
      { omegaSig = omegaSigᵛ
      ; infinityLaws = infinityLawsᵛ
      }
