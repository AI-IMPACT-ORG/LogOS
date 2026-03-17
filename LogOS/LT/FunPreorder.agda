{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.FunPreorder where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Pointwise refinement on function spaces.
--
-- This is used for:
-- - probe suites (many probes combined into one view), and
-- - decoded observation of morphisms (`obs : Code → bnd`) as a function-valued view.
--
-- Extensionality ladder:
-- pointwise comparison → mutual refinement in `FunPreorder`/`DFunPreorder` →
-- strict function equality only after an explicit `Globalise` assumption.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; _≈_; refl⊑)

-- Dependent variant: pointwise refinement where the codomain preorder varies
-- with the index.
DFunPreorder
  : ∀ {ℓA ℓOCon ℓORel}
  → (A : Set ℓA)
  → (O : A → ConPreorder ℓOCon ℓORel)
  → ConPreorder (ℓA ⊔ ℓOCon) (ℓA ⊔ ℓORel)
DFunPreorder A O =
  record
    { Con   = (a : A) → Con (O a)
    ; _⊑_   = λ F G → ∀ a → _⊑_ (O a) (F a) (G a)
    ; refl  = λ {F} a → refl⊑ (O a)
    ; trans = λ {F} {G} {H} FG GH a →
        let
          module R = LogOS.Prelude.RefinementKit.Reasoning (O a)
        in
        R._⊑⟨_⟩_ (F a) (FG a) (GH a)
    }

-- Uniform (constant-family) special case.
FunPreorder
  : ∀ {ℓA ℓOCon ℓORel}
  → (A : Set ℓA)
  → (O : ConPreorder ℓOCon ℓORel)
  → ConPreorder (ℓA ⊔ ℓOCon) (ℓA ⊔ ℓORel)
FunPreorder A O = DFunPreorder A (λ _ → O)

-- --------------------------------------------------------------------------
-- Refinement helpers for function-space preorders.

-- Pointwise equality implies mutual refinement in `DFunPreorder`, without needing
-- any function extensionality principle. If you need pointwise equality to imply
-- propositional equality of functions, use `LogOS.Ports.Globalise`.
pointwise≡→≈
  : ∀ {ℓA ℓOCon ℓORel}
    {A : Set ℓA}
    {O : A → ConPreorder ℓOCon ℓORel}
    {F G : Con (DFunPreorder A O)}
  → (∀ a → F a ≡ G a)
  → _≈_ (DFunPreorder A O) F G
pointwise≡→≈ {O = O} {F = F} {G = G} eq =
  ( forward , backward )
  where
    forward : ∀ a → _⊑_ (O a) (F a) (G a)
    forward a rewrite eq a = refl⊑ (O a)

    backward : ∀ a → _⊑_ (O a) (G a) (F a)
    backward a rewrite sym (eq a) = refl⊑ (O a)
