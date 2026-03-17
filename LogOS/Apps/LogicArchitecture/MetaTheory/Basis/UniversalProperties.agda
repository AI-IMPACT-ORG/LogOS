{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.LogicArchitecture.MetaTheory.Basis.UniversalProperties where

-- MetaTheory — Universal properties for approximation (reflection/forcedness).
--
-- This module packages small “adjunction-style” facts:
-- - inclusion of refinement relations induces canonical Thin2Functors,
-- - the approximation map `shadowApprox` is exactly such an inclusion map
--   from the canonical shadow.

open import LogOS.Prelude
open import LogOS.LT.Thin2Functor using (idThin2Functor)

open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.TwoCellOps using (TwoCellOps)
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Shadow using
  ( RefinementShadow
  ; Shadow≤
  ; shadowThin2Cat
  ; canonicalShadow
  ; shadowApprox
  ; shadowWeaken
  )

-- The approximation map is the weakening functor out of the canonical shadow.
shadowApprox-asWeaken
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓRel}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    (Sh : RefinementShadow {ℓRel = ℓRel} C)
  → shadowApprox Sh ≡ shadowWeaken {S = canonicalShadow C} {T = Sh} (RefinementShadow.sound Sh)
shadowApprox-asWeaken _ = refl

shadowWeaken-refl
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓRel}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    (Sh : RefinementShadow {ℓRel = ℓRel} C)
  → shadowWeaken {S = Sh} {T = Sh} (λ le → le) ≡ idThin2Functor (shadowThin2Cat Sh)
shadowWeaken-refl _ = refl

-- Convenience: for a given shadow `S`, `RefinementShadow.sound S` is exactly
-- the evidence that the canonical shadow is ≤ S.
canonical≤
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓRel}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    (S : RefinementShadow {ℓRel = ℓRel} C)
  → Shadow≤ (canonicalShadow C) S
canonical≤ S = RefinementShadow.sound S
