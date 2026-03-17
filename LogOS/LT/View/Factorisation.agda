{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.View.Factorisation where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- View factorisation: one observation is obtained from another by an explicit
-- monotone collapse map on the observed boundary.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using
  ( ConPreorder
  ; Con
  ; MonoMap
  ; monoMap-≈
  ; refl⊑
  ; _⊑_
  ; _≈_
  )
open import LogOS.LT.View using
  ( View
  ; μ
  ; idView
  ; pullbackView
  )

record FactorisesThrough
  {ℓX ℓC₁ ℓR₁ ℓC₂ ℓR₂ : Level}
  {X : Set ℓX}
  {O₁ : ConPreorder ℓC₁ ℓR₁}
  {O₂ : ConPreorder ℓC₂ ℓR₂}
  (V₁ : View X O₁)
  (V₂ : View X O₂)
  : Set (lsuc (ℓX ⊔ ℓC₁ ⊔ ℓR₁ ⊔ ℓC₂ ⊔ ℓR₂))
  where
  field
    collapse : Con O₁ → Con O₂
    collapse-mono : MonoMap O₁ O₂ collapse
    commute : ∀ x → _≈_ O₂ (μ V₂ x) (collapse (μ V₁ x))

open FactorisesThrough public

collapse-private⊑public
  : ∀ {ℓX ℓC₁ ℓR₁ ℓC₂ ℓR₂ : Level}
    {X : Set ℓX}
    {O₁ : ConPreorder ℓC₁ ℓR₁}
    {O₂ : ConPreorder ℓC₂ ℓR₂}
    {V₁ : View X O₁}
    {V₂ : View X O₂}
  → (F : FactorisesThrough V₁ V₂)
  → (x : X)
  → _⊑_ O₂ (μ V₂ x) (collapse F (μ V₁ x))
collapse-private⊑public F x = fst (commute F x)

collapse-private≈public
  : ∀ {ℓX ℓC₁ ℓR₁ ℓC₂ ℓR₂ : Level}
    {X : Set ℓX}
    {O₁ : ConPreorder ℓC₁ ℓR₁}
    {O₂ : ConPreorder ℓC₂ ℓR₂}
    {V₁ : View X O₁}
    {V₂ : View X O₂}
  → (F : FactorisesThrough V₁ V₂)
  → (x : X)
  → _≈_ O₂ (μ V₂ x) (collapse F (μ V₁ x))
collapse-private≈public F = commute F

factorises-⊑
  : ∀ {ℓX ℓC₁ ℓR₁ ℓC₂ ℓR₂ : Level}
    {X : Set ℓX}
    {O₁ : ConPreorder ℓC₁ ℓR₁}
    {O₂ : ConPreorder ℓC₂ ℓR₂}
    {V₁ : View X O₁}
    {V₂ : View X O₂}
  → (F : FactorisesThrough V₁ V₂)
  → ∀ {x y}
  → _⊑_ O₁ (μ V₁ x) (μ V₁ y)
  → _⊑_ O₂ (μ V₂ x) (μ V₂ y)
factorises-⊑ {O₂ = O₂} {V₁ = V₁} {V₂ = V₂} F {x} {y} x≤y =
  let
    module R = LogOS.Prelude.RefinementKit.Reasoning O₂
  in
  R.begin⊑
    μ V₂ x
      R.⊑⟨ fst (commute F x) ⟩
    collapse F (μ V₁ x)
      R.⊑⟨ collapse-mono F x≤y ⟩
    collapse F (μ V₁ y)
      R.⊑⟨ snd (commute F y) ⟩
    μ V₂ y R.∎⊑

factorises-≈
  : ∀ {ℓX ℓC₁ ℓR₁ ℓC₂ ℓR₂ : Level}
    {X : Set ℓX}
    {O₁ : ConPreorder ℓC₁ ℓR₁}
    {O₂ : ConPreorder ℓC₂ ℓR₂}
    {V₁ : View X O₁}
    {V₂ : View X O₂}
  → (F : FactorisesThrough V₁ V₂)
  → ∀ {x y}
  → _≈_ O₁ (μ V₁ x) (μ V₁ y)
  → _≈_ O₂ (μ V₂ x) (μ V₂ y)
factorises-≈ F (xy , yx) = (factorises-⊑ F xy , factorises-⊑ F yx)

idFactorisation
  : ∀ {ℓX ℓC ℓR : Level}
    {X : Set ℓX}
    {O : ConPreorder ℓC ℓR}
  → (V : View X O)
  → FactorisesThrough V V
idFactorisation {O = O} V =
  record
    { collapse = λ x → x
    ; collapse-mono = λ le → le
    ; commute = λ x → (refl⊑ O , refl⊑ O)
    }

compFactorisation
  : ∀ {ℓX ℓC₁ ℓR₁ ℓC₂ ℓR₂ ℓC₃ ℓR₃ : Level}
    {X : Set ℓX}
    {O₁ : ConPreorder ℓC₁ ℓR₁}
    {O₂ : ConPreorder ℓC₂ ℓR₂}
    {O₃ : ConPreorder ℓC₃ ℓR₃}
    {V₁ : View X O₁}
    {V₂ : View X O₂}
    {V₃ : View X O₃}
  → FactorisesThrough V₁ V₂
  → FactorisesThrough V₂ V₃
  → FactorisesThrough V₁ V₃
compFactorisation {O₂ = O₂} {O₃ = O₃} {V₁ = V₁} {V₂ = V₂} {V₃ = V₃} F₁₂ F₂₃ =
  record
    { collapse = λ x → collapse F₂₃ (collapse F₁₂ x)
    ; collapse-mono = λ le → collapse-mono F₂₃ (collapse-mono F₁₂ le)
    ; commute = λ x →
        let
          module R = LogOS.Prelude.RefinementKit.Reasoning O₃
          open R using (begin≈_; _≈⟨_⟩_; _∎≈)

          step₁ : _≈_ O₃ (μ V₃ x) (collapse F₂₃ (μ V₂ x))
          step₁ = commute F₂₃ x

          step₂
            : _≈_ O₃
                (collapse F₂₃ (μ V₂ x))
                (collapse F₂₃ (collapse F₁₂ (μ V₁ x)))
          step₂ =
            monoMap-≈
              {CP₁ = O₂}
              {CP₂ = O₃}
              {f = collapse F₂₃}
              (collapse-mono F₂₃)
              (μ V₂ x)
              (collapse F₁₂ (μ V₁ x))
              (commute F₁₂ x)
        in
        begin≈
          μ V₃ x ≈⟨ step₁ ⟩
          collapse F₂₃ (μ V₂ x) ≈⟨ step₂ ⟩
          collapse F₂₃ (collapse F₁₂ (μ V₁ x)) ∎≈
    }

mapFactorisation
  : ∀ {ℓC₁ ℓR₁ ℓC₂ ℓR₂ : Level}
    {O₁ : ConPreorder ℓC₁ ℓR₁}
    {O₂ : ConPreorder ℓC₂ ℓR₂}
    (f : Con O₁ → Con O₂)
  → MonoMap O₁ O₂ f
  → FactorisesThrough (idView O₁) (pullbackView f (idView O₂))
mapFactorisation {O₁ = O₁} {O₂ = O₂} f monoF =
  record
    { collapse = f
    ; collapse-mono = monoF
    ; commute = λ x → (refl⊑ O₂ , refl⊑ O₂)
    }
