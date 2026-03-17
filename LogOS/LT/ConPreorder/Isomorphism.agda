{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.ConPreorder.Isomorphism where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Pure order-isomorphism vocabulary on refinement preorders.
--
-- This is LT-level structure: no physical interpretation is built in.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using
  ( ConPreorder
  ; Con
  ; MonoOn
  ; monoMap-≈
  ; _≈_
  ; ≈-sym
  ; ≈-refl
  )

private
  module ≤-Reasoning = LogOS.Prelude.RefinementKit.Reasoning

record OrderIso {ℓCon ℓRel : Level} (O : ConPreorder ℓCon ℓRel)
  : Set (lsuc (ℓCon ⊔ ℓRel)) where
  field
    f : Con O → Con O
    g : Con O → Con O

    f-mono : MonoOn O f
    g-mono : MonoOn O g

    fg≈id : ∀ x → _≈_ O (f (g x)) x
    gf≈id : ∀ x → _≈_ O (g (f x)) x

open OrderIso public

mono-≈
  : ∀ {ℓCon ℓRel : Level} {O : ConPreorder ℓCon ℓRel}
    {f : Con O → Con O}
  → MonoOn O f
  → (x y : Con O)
  → _≈_ O x y
  → _≈_ O (f x) (f y)
mono-≈ {O = O} {f = f} monoF x y eq =
  monoMap-≈ {CP₁ = O} {CP₂ = O} {f = f} monoF x y eq

idOrderIso : ∀ {ℓCon ℓRel : Level} {O : ConPreorder ℓCon ℓRel} → OrderIso O
idOrderIso {O = O} =
  record
    { f = λ x → x
    ; g = λ x → x
    ; f-mono = λ le → le
    ; g-mono = λ le → le
    ; fg≈id = λ x → ≈-refl O x
    ; gf≈id = λ x → ≈-refl O x
    }

compOrderIso
  : ∀ {ℓCon ℓRel : Level} {O : ConPreorder ℓCon ℓRel}
  → OrderIso O → OrderIso O → OrderIso O
compOrderIso {O = O} i₁ i₂ =
  let
    module R = ≤-Reasoning O
    open R using (begin≈_; _≈⟨_⟩_; _∎≈)
  in
  record
    { f = λ x → f i₂ (f i₁ x)
    ; g = λ x → g i₁ (g i₂ x)
    ; f-mono = λ le → f-mono i₂ (f-mono i₁ le)
    ; g-mono = λ le → g-mono i₁ (g-mono i₂ le)
    ; fg≈id =
        λ x →
          let
            step₁ : _≈_ O (f i₁ (g i₁ (g i₂ x))) (g i₂ x)
            step₁ = fg≈id i₁ (g i₂ x)

            step₂ : _≈_ O (f i₂ (f i₁ (g i₁ (g i₂ x)))) (f i₂ (g i₂ x))
            step₂ =
              mono-≈ {O = O} {f = f i₂}
                (f-mono i₂)
                (f i₁ (g i₁ (g i₂ x)))
                (g i₂ x)
                step₁

            step₃ : _≈_ O (f i₂ (g i₂ x)) x
            step₃ = fg≈id i₂ x
          in
          begin≈
            f i₂ (f i₁ (g i₁ (g i₂ x))) ≈⟨ step₂ ⟩
            f i₂ (g i₂ x) ≈⟨ step₃ ⟩
            x ∎≈
    ; gf≈id =
        λ x →
          let
            step₁ : _≈_ O (g i₂ (f i₂ (f i₁ x))) (f i₁ x)
            step₁ = gf≈id i₂ (f i₁ x)

            step₂ : _≈_ O (g i₁ (g i₂ (f i₂ (f i₁ x)))) (g i₁ (f i₁ x))
            step₂ =
              mono-≈ {O = O} {f = g i₁}
                (g-mono i₁)
                (g i₂ (f i₂ (f i₁ x)))
                (f i₁ x)
                step₁

            step₃ : _≈_ O (g i₁ (f i₁ x)) x
            step₃ = gf≈id i₁ x
          in
          begin≈
            g i₁ (g i₂ (f i₂ (f i₁ x))) ≈⟨ step₂ ⟩
            g i₁ (f i₁ x) ≈⟨ step₃ ⟩
            x ∎≈
    }

orderIso-reflects-≈
  : ∀ {ℓCon ℓRel : Level} {O : ConPreorder ℓCon ℓRel}
  → (i : OrderIso O)
  → (x y : Con O)
  → _≈_ O (f i x) (f i y)
  → _≈_ O x y
orderIso-reflects-≈ {O = O} i x y eq =
  let
    module R = ≤-Reasoning O
    open R using (begin≈_; _≈⟨_⟩_; _∎≈)

    step₁ : _≈_ O x (g i (f i x))
    step₁ = ≈-sym {CP = O} (gf≈id i x)

    step₂ : _≈_ O (g i (f i x)) (g i (f i y))
    step₂ =
      mono-≈
        {O = O}
        {f = g i}
        (g-mono i)
        (f i x)
        (f i y)
        eq

    step₃ : _≈_ O (g i (f i y)) y
    step₃ = gf≈id i y
  in
  begin≈
    x ≈⟨ step₁ ⟩
    g i (f i x) ≈⟨ step₂ ⟩
    g i (f i y) ≈⟨ step₃ ⟩
    y ∎≈

collapse-obstructs-orderIso
  : ∀ {ℓCon ℓRel : Level} {O : ConPreorder ℓCon ℓRel}
  → (i : OrderIso O)
  → (x y : Con O)
  → ¬ _≈_ O x y
  → ¬ _≈_ O (f i x) (f i y)
collapse-obstructs-orderIso i x y x≉y fx≈fy =
  x≉y (orderIso-reflects-≈ i x y fx≈fy)
