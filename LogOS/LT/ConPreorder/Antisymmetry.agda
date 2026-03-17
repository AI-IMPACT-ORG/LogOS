{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.ConPreorder.Antisymmetry where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Antisymmetry as an explicit assumption/port on a preorder.
--
-- In LogOS, strict equalities are treated as S-tier checks; this record is the
-- minimal “classical-limit” payload that collapses `≈` into `≡` when needed.
-- (“Classical limit” here means extensional/posetal collapse, not classical logic/LEM.)

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; _≈_)

record Antisymmetry {ℓCon ℓRel : Level} (CP : ConPreorder ℓCon ℓRel)
  : Set (lsuc (ℓCon ⊔ ℓRel)) where
  field
    antisym : ∀ {x y : Con CP} → _⊑_ CP x y → _⊑_ CP y x → x ≡ y

  ≈→≡ : ∀ {x y : Con CP} → _≈_ CP x y → x ≡ y
  ≈→≡ xy = antisym (fst xy) (snd xy)

open Antisymmetry public
