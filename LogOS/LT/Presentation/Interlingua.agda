{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Presentation.Interlingua where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Minimal “interlingua” theorem surface (1.1).
--
-- The semantic boundary preorder is the interlingua.
--
-- A view fixes observation; a presentation is any internal relation that respects
-- with that view (`LogOS.LT.Presentation`). Any translation that preserves
-- boundary meaning (up to mutual refinement) automatically:
-- - is monotone w.r.t. the induced pullback refinements, and
-- - transports any observation-extensional property.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; _⊑_; _≈_)
open import LogOS.LT.View using (View; μ; _⊑[_]_; Extensional≈)
private
  module CPReasoning = LogOS.Prelude.RefinementKit.Reasoning
open import LogOS.LT.Presentation using (Presentation)
open import LogOS.LT.Derivability using (DerivationSystem)
open import LogOS.LT.Presentation.Transport using (pullback-Extensional≈)

record Translation
  {ℓX₁ ℓX₂ ℓTCon ℓTRel : Level}
  {X₁ : Set ℓX₁} {X₂ : Set ℓX₂}
  (T : ConPreorder ℓTCon ℓTRel)
  (V₁ : View X₁ T)
  (V₂ : View X₂ T)
  : Set (lsuc (ℓX₁ ⊔ ℓX₂ ⊔ ℓTCon ⊔ ℓTRel)) where
  field
    map       : X₁ → X₂
    preserves : ∀ x → _≈_ T (μ V₂ (map x)) (μ V₁ x)

open Translation public
-- Translation is monotone for the pullback refinements.
translate-mono
  : ∀ {ℓX₁ ℓX₂ ℓTCon ℓTRel}
    {X₁ : Set ℓX₁} {X₂ : Set ℓX₂}
    {T : ConPreorder ℓTCon ℓTRel}
    {V₁ : View X₁ T} {V₂ : View X₂ T}
  → (tr : Translation T V₁ V₂)
  → ∀ {x y} → x ⊑[ V₁ ] y → map tr x ⊑[ V₂ ] map tr y
translate-mono {T = T} {V₁ = V₁} {V₂ = V₂} tr {x} {y} x≤y =
  let
    module R = CPReasoning T
    open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
    mx≤x : _⊑_ T (μ V₂ (map tr x)) (μ V₁ x)
    mx≤x = fst (preserves tr x)

    y≤my : _⊑_ T (μ V₁ y) (μ V₂ (map tr y))
    y≤my = snd (preserves tr y)
  in
  begin⊑
    μ V₂ (map tr x) ⊑⟨ mx≤x ⟩
    μ V₁ x ⊑⟨ x≤y ⟩
    μ V₁ y ⊑⟨ y≤my ⟩
    μ V₂ (map tr y) ∎⊑

-- Extensional properties transport along a translation.
translate-extensional
  : ∀ {ℓX₁ ℓX₂ ℓTCon ℓTRel ℓP}
    {X₁ : Set ℓX₁} {X₂ : Set ℓX₂}
    {T : ConPreorder ℓTCon ℓTRel}
    {V₁ : View X₁ T} {V₂ : View X₂ T}
  → (tr : Translation T V₁ V₂)
  → (P₂ : X₂ → Set ℓP)
  → Extensional≈ V₂ P₂
  → Extensional≈ V₁ (λ x → P₂ (map tr x))
translate-extensional {T = T} {V₁ = V₁} {V₂ = V₂} tr P₂ ext₂ =
  pullback-Extensional≈ V₁ V₂ (map tr) (preserves tr) P₂ ext₂

-- --------------------------------------------------------------------------
-- Transport presentations (“proof systems”) along translations.
--
-- If V₁ and V₂ present the same boundary meaning up to mutual refinement, then
-- any V₂-observation-respecting implementation relation can be pulled back along the
-- translation map to a V₁-observation-respecting one.

pullbackPresentation
  : ∀ {ℓX₁ ℓX₂ ℓTCon ℓTRel ℓR}
    {X₁ : Set ℓX₁} {X₂ : Set ℓX₂}
    {T : ConPreorder ℓTCon ℓTRel}
    {V₁ : View X₁ T} {V₂ : View X₂ T}
  → (tr : Translation T V₁ V₂)
  → Presentation {ℓR = ℓR} V₂
  → Presentation {ℓR = ℓR} V₁
pullbackPresentation {T = T} {V₁ = V₁} {V₂ = V₂} tr P₂ =
  record
    { _≼_ = λ x y → Presentation._≼_ P₂ (map tr x) (map tr y)
    ; refl≼ = Presentation.refl≼ P₂
    ; trans≼ = Presentation.trans≼ P₂
    ; observe-mono = λ {x} {y} x≼y →
        let
          module R = CPReasoning T
          open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
          mx≤my : _⊑_ T (μ V₂ (map tr x)) (μ V₂ (map tr y))
          mx≤my = Presentation.observe-mono P₂ x≼y

          x≤mx : _⊑_ T (μ V₁ x) (μ V₂ (map tr x))
          x≤mx = snd (preserves tr x)

          my≤y : _⊑_ T (μ V₂ (map tr y)) (μ V₁ y)
          my≤y = fst (preserves tr y)
        in
        begin⊑
          μ V₁ x ⊑⟨ x≤mx ⟩
          μ V₂ (map tr x) ⊑⟨ mx≤my ⟩
          μ V₂ (map tr y) ⊑⟨ my≤y ⟩
          μ V₁ y ∎⊑
    }

-- Pull back a derivation system (base assumption + observation-respecting presentation).
pullbackDerivationSystem
  : ∀ {ℓX₁ ℓX₂ ℓTCon ℓTRel ℓR}
    {X₁ : Set ℓX₁} {X₂ : Set ℓX₂}
    {T : ConPreorder ℓTCon ℓTRel}
    {V₁ : View X₁ T} {V₂ : View X₂ T}
  → (tr : Translation T V₁ V₂)
  → DerivationSystem {ℓR = ℓR} V₂
  → (base₁ : X₁)
  → DerivationSystem {ℓR = ℓR} V₁
pullbackDerivationSystem tr S₂ base₁ =
  record
    { presentation = pullbackPresentation tr (DerivationSystem.presentation S₂)
    ; base = base₁
    }
