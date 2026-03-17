{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Presentation.Transport where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Transport lemmas for meaning-preserving translations.
--
-- These lemmas package the generic proof pattern:
-- - only the observed boundary meaning matters (extensionality), and
-- - once a translation preserves meaning (up to refinement), properties and
--   invariance facts transport automatically.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; ↔-trans)
open import LogOS.LT.ConPreorder using (ConPreorder; _⊑_; _≈_; ≈-sym)
open import LogOS.LT.View using
  ( View
  ; μ
  ; _≈[_]_
  ; Extensional≈
  ; Extensional≈-cong
  ; ExtensionalRel≈
  )
open import LogOS.LT.View.Roles using (forget)
open import LogOS.LT.Kernel using (Kernel; bnd; Code; decode; decodeView)
open import LogOS.LT.Hom.Core using (KernelHom; mapCode; map∂; map∂-mono; decode-mapCode≈)
private
  module ≤-Reasoning = LogOS.Prelude.RefinementKit.Reasoning

-- --------------------------------------------------------------------------
-- Generic step-invariance notion (observer-core style).

InvariantUnder
  : ∀ {ℓX ℓP : Level}
    {X : Set ℓX}
  → (step : X → X)
  → (P : X → Set ℓP)
  → Set (ℓX ⊔ ℓP)
InvariantUnder step P = ∀ x → P x ↔ P (step x)

-- --------------------------------------------------------------------------
-- Transport extensionality along a meaning-preserving translation.

pullback-Extensional≈
  : ∀ {ℓX₁ ℓX₂ ℓTCon ℓTRel ℓP : Level}
    {X₁ : Set ℓX₁} {X₂ : Set ℓX₂}
    {T : ConPreorder ℓTCon ℓTRel}
  → (V₁ : View X₁ T)
  → (V₂ : View X₂ T)
  → (map : X₁ → X₂)
  → (map-μ≈ : ∀ x → _≈_ T (μ V₂ (map x)) (μ V₁ x))
  → (P₂ : X₂ → Set ℓP)
  → Extensional≈ V₂ P₂
  → Extensional≈ V₁ (λ x → P₂ (map x))
pullback-Extensional≈ {T = T} V₁ V₂ map map-μ≈ P₂ ext₂ x y eq p =
  let
    module R = ≤-Reasoning T
    open R using (begin≈_; _≈⟨_⟩_; _∎≈)

    eq₁   = map-μ≈ x
    eq₂   = map-μ≈ y
    eqmap =
      begin≈
        μ V₂ (map x) ≈⟨ eq₁ ⟩
        μ V₁ x ≈⟨ eq ⟩
        μ V₁ y ≈⟨ ≈-sym {CP = T} eq₂ ⟩
        μ V₂ (map y) ∎≈
  in
  ext₂ (map x) (map y) eqmap p

pullback-ExtensionalRel≈
  : ∀ {ℓX₁ ℓX₂ ℓTCon ℓTRel ℓR : Level}
    {X₁ : Set ℓX₁} {X₂ : Set ℓX₂}
    {T : ConPreorder ℓTCon ℓTRel}
  → (V₁ : View X₁ T)
  → (V₂ : View X₂ T)
  → (map : X₁ → X₂)
  → (map-μ≈ : ∀ x → _≈_ T (μ V₂ (map x)) (μ V₁ x))
  → (R₂ : X₂ → X₂ → Set ℓR)
  → ExtensionalRel≈ V₂ R₂
  → ExtensionalRel≈ V₁ (λ x y → R₂ (map x) (map y))
pullback-ExtensionalRel≈ {T = T} V₁ V₂ map map-μ≈ R₂ ext₂ x x' y y' xx' yy' rxy =
  let
    module R = ≤-Reasoning T
    open R using (begin≈_; _≈⟨_⟩_; _∎≈)

    eqx =
      begin≈
        μ V₂ (map x) ≈⟨ map-μ≈ x ⟩
        μ V₁ x ≈⟨ xx' ⟩
        μ V₁ x' ≈⟨ ≈-sym {CP = T} (map-μ≈ x') ⟩
        μ V₂ (map x') ∎≈

    eqy =
      begin≈
        μ V₂ (map y) ≈⟨ map-μ≈ y ⟩
        μ V₁ y ≈⟨ yy' ⟩
        μ V₁ y' ≈⟨ ≈-sym {CP = T} (map-μ≈ y') ⟩
        μ V₂ (map y') ∎≈
  in
  ext₂ (map x) (map x') (map y) (map y') eqx eqy rxy

-- Transport step-invariance under a step transformer when the translation
-- commutes with the step up to observed meaning.
pullback-InvariantUnder≈
  : ∀ {ℓX₁ ℓX₂ ℓTCon ℓTRel ℓP : Level}
    {X₁ : Set ℓX₁} {X₂ : Set ℓX₂}
    {T : ConPreorder ℓTCon ℓTRel}
  → (V₂ : View X₂ T)
  → (map : X₁ → X₂)
  → (step₁ : X₁ → X₁)
  → (step₂ : X₂ → X₂)
  → (P₂ : X₂ → Set ℓP)
  → (∀ x → step₂ (map x) ≈[ V₂ ] map (step₁ x))
  → Extensional≈ V₂ P₂
  → InvariantUnder step₂ P₂
  → InvariantUnder step₁ (λ x → P₂ (map x))
pullback-InvariantUnder≈ V₂ map step₁ step₂ P₂ eqStep ext₂ inv₂ x =
  ↔-trans
    (inv₂ (map x))
    (Extensional≈-cong {V = V₂} {P = P₂} ext₂ (eqStep x))

-- --------------------------------------------------------------------------
-- KernelHom specialisation: transport extensionality across a translation.

-- If a property on target code depends only on the decoded boundary meaning,
-- it can be pulled back along any kernel morphism.
pullback-mapCode-Extensional≈
  : ∀ {ℓ ℓRel ℓCode ℓCode' ℓP : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → (h : KernelHom K K')
  → (P' : Code K' → Set ℓP)
  → Extensional≈ (forget (decodeView K')) P'
  → Extensional≈ (forget (decodeView K)) (λ γ → P' (mapCode h γ))
pullback-mapCode-Extensional≈ {K = K} {K' = K'} h P' extP γ δ (γ≤δ , δ≤γ) p =
  extP (mapCode h γ) (mapCode h δ) eqmap p
  where
    CP' = bnd K'

    V' = forget (decodeView K')

    decode-mapγ≤decode-mapδ
      : _⊑_ CP' (decode K' (mapCode h γ)) (decode K' (mapCode h δ))
    decode-mapγ≤decode-mapδ =
      let
        module R = ≤-Reasoning CP'
        open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
      in
      begin⊑
        decode K' (mapCode h γ)
          ⊑⟨ fst (decode-mapCode≈ h γ) ⟩
        map∂ h (decode K γ)
          ⊑⟨ map∂-mono h γ≤δ ⟩
        map∂ h (decode K δ)
          ⊑⟨ snd (decode-mapCode≈ h δ) ⟩
        decode K' (mapCode h δ) ∎⊑

    decode-mapδ≤decode-mapγ
      : _⊑_ CP' (decode K' (mapCode h δ)) (decode K' (mapCode h γ))
    decode-mapδ≤decode-mapγ =
      let
        module R = ≤-Reasoning CP'
        open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
      in
      begin⊑
        decode K' (mapCode h δ)
          ⊑⟨ fst (decode-mapCode≈ h δ) ⟩
        map∂ h (decode K δ)
          ⊑⟨ map∂-mono h δ≤γ ⟩
        map∂ h (decode K γ)
          ⊑⟨ snd (decode-mapCode≈ h γ) ⟩
        decode K' (mapCode h γ) ∎⊑

    eqmap : (mapCode h γ) ≈[ V' ] (mapCode h δ)
    eqmap = (decode-mapγ≤decode-mapδ , decode-mapδ≤decode-mapγ)

-- KernelHom convenience: decoded mutual refinement transports across `mapCode`.
mapCode-preserves-decode≈
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    (h : KernelHom K K')
    {γ₁ γ₂ : Code K}
  → _≈_ (bnd K) (decode K γ₁) (decode K γ₂)
  → _≈_ (bnd K') (decode K' (mapCode h γ₁)) (decode K' (mapCode h γ₂))
mapCode-preserves-decode≈ {K = K} {K' = K'} h {γ₁ = γ₁} {γ₂ = γ₂} (γ₁≤γ₂ , γ₂≤γ₁) =
  ( mapCode-preserves-decode⊑ {γa = γ₁} {γb = γ₂} γ₁≤γ₂
  , mapCode-preserves-decode⊑ {γa = γ₂} {γb = γ₁} γ₂≤γ₁
  )
  where
    CP' = bnd K'

    mapCode-preserves-decode⊑
      : ∀ {γa γb}
      → _⊑_ (bnd K) (decode K γa) (decode K γb)
      → _⊑_ CP' (decode K' (mapCode h γa)) (decode K' (mapCode h γb))
    mapCode-preserves-decode⊑ {γa = γa} {γb = γb} γa≤γb =
      let
        module R = ≤-Reasoning CP'
        open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
      in
      begin⊑
        decode K' (mapCode h γa)
          ⊑⟨ fst (decode-mapCode≈ h γa) ⟩
        map∂ h (decode K γa)
          ⊑⟨ map∂-mono h γa≤γb ⟩
        map∂ h (decode K γb)
          ⊑⟨ snd (decode-mapCode≈ h γb) ⟩
        decode K' (mapCode h γb) ∎⊑

pullback-mapCode-ExtensionalRel≈
  : ∀ {ℓ ℓRel ℓCode ℓCode' ℓR : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → (h : KernelHom K K')
  → (R' : Code K' → Code K' → Set ℓR)
  → ExtensionalRel≈ (forget (decodeView K')) R'
  → ExtensionalRel≈ (forget (decodeView K)) (λ γ δ → R' (mapCode h γ) (mapCode h δ))
pullback-mapCode-ExtensionalRel≈ h R' extR γ γ' δ δ' γγ' δδ' r =
  extR
    (mapCode h γ)
    (mapCode h γ')
    (mapCode h δ)
    (mapCode h δ')
    (mapCode-preserves-decode≈ h γγ')
    (mapCode-preserves-decode≈ h δδ')
    r
