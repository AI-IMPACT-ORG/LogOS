{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ShadowInitiality where

-- MetaTheory — Contextual shadow initiality (forcedness by observation).
--
-- Reading: once a view/observable context is fixed, the induced shadow is the
-- coarsest refinement shadow respecting that observation.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder)
open import LogOS.LT.View using (_⊑[_]_)

open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.TwoCellOps using (TwoCellOps)
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Shadow using
  ( RefinementShadow
  ; Shadow≤
  )
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ShadowByView using
  ( ShadowByView
  ; shadowFromView
  )

ShadowForcedByView
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓRel ℓOCon ℓORel}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    {O : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon ℓORel}
  → (S : ShadowByView C O)
  → (R : RefinementShadow {ℓRel = ℓRel} C)
  → (μ-soundR :
        ∀ {A B} {f g : TwoCellOps.Hom₁ C A B}
      → RefinementShadow._⊑̂_ R f g
      → f ⊑[ ShadowByView.μ S {A} {B} ] g)
  → Shadow≤ R (shadowFromView S)
ShadowForcedByView _ _ μ-soundR le = μ-soundR le
