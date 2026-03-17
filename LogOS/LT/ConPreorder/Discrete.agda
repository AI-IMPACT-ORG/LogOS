{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.ConPreorder.Discrete where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Equality as the finest observational preorder.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; _≈_)

DiscretePreorder : ∀ {ℓ} → Set ℓ → ConPreorder ℓ ℓ
DiscretePreorder A =
  record
    { Con = A
    ; _⊑_ = _≡_
    ; refl = refl
    ; trans = trans
    }

refl⊑
  : ∀ {ℓ} {A : Set ℓ}
  → (x : A)
  → LogOS.Prelude.RefinementKit._⊑_ (DiscretePreorder A) x x
refl⊑ _ = refl

≡→≈
  : ∀ {ℓ} {A : Set ℓ} {x y : A}
  → x ≡ y
  → _≈_ (DiscretePreorder A) x y
≡→≈ eq = (eq , sym eq)
