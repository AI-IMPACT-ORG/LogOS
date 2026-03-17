{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.TypeTheory.Surface where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Surface aliases (ergonomic layer) over the LT spine.
--
-- This module is intentionally shallow: it adds no axioms and does not change
-- the meaning of refinement; it just repackages existing LT definitions with
-- type-theory-flavoured names.
--
-- Coherence note:
-- the LT morphism spine is coherence-indexed (`CohMode`). The type-theory
-- facade now keeps that index explicit in `Tm`; `Tm≈` and `Tm⊑` remain the
-- common refinements-first specialisations.

open import LogOS.Prelude
open import LogOS.LT.Coherence using (CohMode; approx; under; CohLevel)
open import LogOS.LT.Kernel using (Kernel)
import LogOS.LT.Hom.Core as Hom

import LogOS.LT.TypeTheory.Core as Core
open Core public

TmLike
  : ∀ {ℓ ℓRel ℓCode₁ ℓCode₂ : Level}
  → (m : CohMode)
  → Kernel ℓ ℓRel ℓCode₁
  → Kernel ℓ ℓRel ℓCode₂
  → Set (lsuc ℓ ⊔ lsuc ℓRel ⊔ ℓCode₁ ⊔ ℓCode₂ ⊔ CohLevel m ℓ ℓRel)
TmLike = Tm

Tm≈
  : ∀ {ℓ ℓRel ℓCode₁ ℓCode₂ : Level}
  → Kernel ℓ ℓRel ℓCode₁
  → Kernel ℓ ℓRel ℓCode₂
  → Set _
Tm≈ = TmLike approx

Tm⊑
  : ∀ {ℓ ℓRel ℓCode₁ ℓCode₂ : Level}
  → Kernel ℓ ℓRel ℓCode₁
  → Kernel ℓ ℓRel ℓCode₂
  → Set _
Tm⊑ = TmLike under
