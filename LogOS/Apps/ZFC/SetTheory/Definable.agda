{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.SetTheory.Definable where

-- Formula-driven "definable set" helpers (stack-first).
--
-- This module is first-order by construction: it works over the explicit
-- first-order (formula-coded) upgrade tower `Stack.ProfileTowerFO`, where
-- Separation/Replacement are schema families indexed by `Proof.Syntax.Formula`
-- codes, and delivered as `View`s into the set boundary preorder.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)
open import LogOS.LT.View using (μ)

import LogOS.Apps.ZFC.Proof.Syntax as Syn using (Formula)
import LogOS.Apps.ZFC.Stack.ProfileTowerFO as TowerFO

module ForZFStackFO₋Fnd {ℓ : Level} (zf : TowerFO.ZFStackFO₋Fnd {ℓ}) where
  open TowerFO.ZFStackFO₋Fnd zf public
  -- Re-export the record-defined “valuation algebra” helpers explicitly, so
  -- users can access them through the definable wrappers (and docs can refer
  -- to them as `Def.Valuation`, `Def.extend`, ...).
  Valuation : Set ℓ
  Valuation = Base.Valuation

  extend : SetU → Valuation → Valuation
  extend = Base.extend

  evalFormula : Syn.Formula → Valuation → Set ℓ
  evalFormula = Base.evalFormula

  FunctionalOnX : Syn.Formula → Valuation → SetU → Set ℓ
  FunctionalOnX = Base.FunctionalOnX

  separateByFormula
    : (P : Syn.Formula)
    → (ρ : Valuation)
    → (x : SetU)
    → Σ SetU (λ y → ∀ z → (z ∈ y) ↔ ((z ∈ x) × evalFormula P (extend z (extend x ρ))))
  separateByFormula P ρ x =
    μ (SeparationFV P ρ) x
    , (λ z → separationF-spec P ρ x z)

  imageByFormula
    : (R : Syn.Formula)
    → (ρ : Valuation)
    → (x : SetU)
    → FunctionalOnX R ρ x
    → Σ SetU (λ y → ∀ z → (z ∈ y) ↔ (Σ SetU (λ u → u ∈ x × evalFormula R (extend u (extend z ρ)))))
  imageByFormula R ρ x fun =
    μ (ReplacementFV R ρ) (x , fun)
    , (λ z → replacementF-spec R ρ x fun z)

module ForZFStackFO {ℓ : Level} (zf : TowerFO.ZFStackFO {ℓ}) where
  open TowerFO.ZFStackFO zf public
  module ZF₋Fnd = ForZFStackFO₋Fnd (TowerFO.forgetFoundation zf)
  open ZF₋Fnd public using
    ( Valuation; extend; evalFormula; FunctionalOnX
    ; separateByFormula; imageByFormula
    )

-- ZFC wrapper: the definable interface depends only on the underlying ZF FO
-- stack, so we re-export it from `ZFCStackFO`.
module ForZFCStackFO {ℓ : Level} (zfc : TowerFO.ZFCStackFO {ℓ}) where
  open TowerFO.ZFCStackFO zfc public
  module ZF = ForZFStackFO zf
  open ZF public using
    ( Valuation; extend; evalFormula; FunctionalOnX
    ; separateByFormula; imageByFormula
    )
