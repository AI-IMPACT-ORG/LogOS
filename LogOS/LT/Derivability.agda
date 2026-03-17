{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Derivability where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Kernel-native derivability / presentation layer.
--
-- A “proof system” is a presentation preorder respecting a chosen
-- observation view. Derivability is refinement in that presentation; semantic
-- soundness is exactly the requirement that presentation steps refine into the
-- canonical pullback refinement along the view.
--
-- This module packages the smallest useful fragment:
-- derivability from a chosen base assumption and the corresponding cut/soundness
-- rules, without fixing any particular syntax of sequents or logical connectives.
-- It is therefore not a sequent calculus unless a downstream pack supplies the
-- judgement form being related.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder)
private
  module ≤-Reasoning = LogOS.Prelude.RefinementKit.Reasoning
open import LogOS.LT.View using (View; μ; _⊑[_]_)
open import LogOS.LT.Presentation using (Presentation; canonicalPresentation; CompletePresentation; fromCanonical)

record DerivationSystem
  {ℓX ℓR ℓOCon ℓORel : Level}
  {X : Set ℓX}
  {O : ConPreorder ℓOCon ℓORel}
  (V : View X O)
  : Set (lsuc (ℓX ⊔ ℓR ⊔ ℓOCon ⊔ ℓORel)) where
  field
    presentation : Presentation {ℓR = ℓR} V
    base         : X

  open Presentation presentation public
  -- “Provable” = derivable from the chosen base assumption.
  Derivable : X → Set ℓR
  Derivable x = base ≼ x

  derivable-refl : Derivable base
  derivable-refl = refl≼

  derivable-cut : ∀ {x y} → Derivable x → x ≼ y → Derivable y
  derivable-cut bx xy = trans≼ bx xy

  -- Soundness: provability implies canonical refinement along the observation view.
  derivable-sound : ∀ {x} → Derivable x → base ⊑[ V ] x
  derivable-sound = toCanonical

  -- Completeness at the chosen base, relative to an explicit completeness witness
  -- for the presentation.
  derivable-complete
    : CompletePresentation presentation
    → ∀ {x} → base ⊑[ V ] x → Derivable x
  derivable-complete C le = fromCanonical C le

-- --------------------------------------------------------------------------
-- Generating a derivation system from primitive rules.
--
-- A “rule set” is a step relation `step : X → X → Set` together with a
-- soundness proof stating each step refines the observed meaning.
--
-- The induced derivability relation is the reflexive-transitive closure of
-- `step`, which is the minimal preorder containing `step`. This gives a
-- presentation (hence a derivation system) by construction.

data Deriv
  {ℓX ℓStep : Level}
  {X : Set ℓX}
  (step : X → X → Set ℓStep)
  : X → X → Set (ℓX ⊔ ℓStep) where
  reflD  : ∀ {x} → Deriv step x x
  stepD  : ∀ {x y} → step x y → Deriv step x y
  transD : ∀ {x y z} → Deriv step x y → Deriv step y z → Deriv step x z

-- Preorder reasoning combinators for `Deriv` (reflexive-transitive closure).
--
-- This is intentionally tiny: use these to keep derivations chain-shaped,
-- without introducing any additional proof-theoretic structure.
module DerivReasoning
  {ℓX ℓStep : Level}
  {X : Set ℓX}
  (step : X → X → Set ℓStep)
  where

  infix  1 beginD_
  infixr 2 _D⟨_⟩_
  infix  3 _∎D

  beginD_ : ∀ {x y} → Deriv step x y → Deriv step x y
  beginD_ d = d

  _D⟨_⟩_ : ∀ x {y z} → Deriv step x y → Deriv step y z → Deriv step x z
  _ D⟨ d₁ ⟩ d₂ = transD d₁ d₂

  _∎D : ∀ x → Deriv step x x
  _∎D _ = reflD

-- Elimination principle: `Deriv step` is the least reflexive-transitive
-- relation containing `step`.
Deriv-elim
  : ∀ {ℓX ℓStep ℓR}
    {X : Set ℓX}
    {step : X → X → Set ℓStep}
    (R : X → X → Set ℓR)
  → (reflR : ∀ {x} → R x x)
  → (transR : ∀ {x y z} → R x y → R y z → R x z)
  → (stepR : ∀ {x y} → step x y → R x y)
  → ∀ {x y} → Deriv step x y → R x y
Deriv-elim R reflR transR stepR reflD = reflR
Deriv-elim R reflR transR stepR (stepD st) = stepR st
Deriv-elim R reflR transR stepR (transD d₁ d₂) =
  transR
    (Deriv-elim R reflR transR stepR d₁)
    (Deriv-elim R reflR transR stepR d₂)

derivPresentation
  : ∀ {ℓX ℓStep ℓOCon ℓORel}
    {X : Set ℓX}
    {O : ConPreorder ℓOCon ℓORel}
    (V : View X O)
  → (step : X → X → Set ℓStep)
  → (sound : ∀ {x y} → step x y → x ⊑[ V ] y)
  → Presentation {ℓR = (ℓX ⊔ ℓStep)} V
derivPresentation {O = O} V step sound =
  record
    { _≼_ = Deriv step
    ; refl≼ = reflD
    ; trans≼ = transD
    ; observe-mono = λ d →
        go d
    }
  where
    go : ∀ {x y} → Deriv step x y → x ⊑[ V ] y
    go reflD = ConPreorder.refl O
    go (stepD st) = sound st
    go {x = x} {y = z} (transD {y = y₁} d₁ d₂) =
      let module R = ≤-Reasoning O in
      R._⊑⟨_⟩_ (μ V x) (go d₁) (go d₂)

-- Bundle: a derived derivation system from primitive steps + a chosen base.
generatedDerivationSystem
  : ∀ {ℓX ℓStep ℓOCon ℓORel}
    {X : Set ℓX}
    {O : ConPreorder ℓOCon ℓORel}
    (V : View X O)
  → (step : X → X → Set ℓStep)
  → (sound : ∀ {x y} → step x y → x ⊑[ V ] y)
  → (base : X)
  → DerivationSystem {ℓR = (ℓX ⊔ ℓStep)} V
generatedDerivationSystem V step sound base =
  record
    { presentation = derivPresentation V step sound
    ; base = base
    }

-- --------------------------------------------------------------------------
-- Canonical derivation system: take pullback refinement along the view as the
-- presentation preorder. This is complete by construction.

canonicalDerivationSystem
  : ∀ {ℓX ℓOCon ℓORel : Level}
    {X : Set ℓX}
    {O : ConPreorder ℓOCon ℓORel}
  → (V : View X O)
  → (base : X)
  → DerivationSystem {ℓR = ℓORel} V
canonicalDerivationSystem V base =
  record
    { presentation = canonicalPresentation V
    ; base = base
    }
