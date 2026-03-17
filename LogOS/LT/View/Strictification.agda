{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.View.Strictification where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con)
open import LogOS.LT.View using (View; μ)
open import LogOS.Syntax.Prop using (_↔_; intro)

infix 4 _≃[_]_
_≃[_]_
  : ∀ {ℓX ℓCon ℓRel} {X : Set ℓX} {T : ConPreorder ℓCon ℓRel}
  → X → View X T → X → Set ℓCon
x ≃[ V ] y = μ V x ≡ μ V y

Extensional≃
  : ∀ {ℓX ℓCon ℓRel ℓP}
    {X : Set ℓX} {T : ConPreorder ℓCon ℓRel}
  → View X T
  → (X → Set ℓP)
  → Set (ℓX ⊔ ℓCon ⊔ ℓP)
Extensional≃ V P = ∀ x y → x ≃[ V ] y → P x → P y

Extensional≃-cong
  : ∀ {ℓX ℓCon ℓRel ℓP}
    {X : Set ℓX} {T : ConPreorder ℓCon ℓRel}
    {V : View X T} {P : X → Set ℓP}
  → Extensional≃ V P
  → ∀ {x y} → x ≃[ V ] y → P x ↔ P y
Extensional≃-cong ext eq =
  intro
    (λ p → ext _ _ eq p)
    (λ p → ext _ _ (sym eq) p)
