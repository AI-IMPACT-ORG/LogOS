{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Bicategory where

-- MetaTheory — Bicategory-shaped presentations (as additional law bundles).
--
-- LogOS alignment:
-- - keep a minimal *operations* basis (`TwoCellOps`),
-- - keep 2-cell-based associator/unitors as an explicit *law bundle*
--   (`TwoCellOpsLaws`),
-- - keep full coherence (pentagon/triangle) as an optional extra bundle.
--
-- This makes explicit that “weak 2-categorical” presentations still factor
-- through the same thin-shadow interface used by the LT stack.

open import LogOS.Prelude
open import LogOS.LT.Thin2Cat using (Thin2Cat; Thin2CatLaws)

open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.TwoCellOps using
  ( TwoCellOps
  ; TwoCellOpsLaws
  ; thinify₂
  ; thinify₂-laws
  )

record BicatW (ℓObj ℓHom₁ ℓHom₂ : Level)
  : Set (lsuc (ℓObj ⊔ ℓHom₁ ⊔ ℓHom₂)) where
  field
    ops : TwoCellOps ℓObj ℓHom₁ ℓHom₂
    laws : TwoCellOpsLaws ops

-- Stable “forgetful” names (now projections).
BicatW→TwoCellOps
  : ∀ {ℓObj ℓHom₁ ℓHom₂}
  → BicatW ℓObj ℓHom₁ ℓHom₂
  → TwoCellOps ℓObj ℓHom₁ ℓHom₂
BicatW→TwoCellOps = BicatW.ops

BicatW→TwoCellOpsLaws
  : ∀ {ℓObj ℓHom₁ ℓHom₂}
    (B : BicatW ℓObj ℓHom₁ ℓHom₂)
  → TwoCellOpsLaws (BicatW→TwoCellOps B)
BicatW→TwoCellOpsLaws = BicatW.laws

BicatW→Thin2Cat
  : ∀ {ℓObj ℓHom₁ ℓHom₂}
  → BicatW ℓObj ℓHom₁ ℓHom₂
  → Thin2Cat ℓObj ℓHom₁ ℓHom₂
BicatW→Thin2Cat B = thinify₂ (BicatW.ops B)

BicatW→Thin2CatLaws
  : ∀ {ℓObj ℓHom₁ ℓHom₂}
    (B : BicatW ℓObj ℓHom₁ ℓHom₂)
  → Thin2CatLaws (BicatW→Thin2Cat B)
BicatW→Thin2CatLaws B =
  thinify₂-laws (BicatW.ops B) (BicatW.laws B)
