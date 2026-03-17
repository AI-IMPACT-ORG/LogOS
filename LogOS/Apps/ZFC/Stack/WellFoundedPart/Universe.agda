{-
  LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
  Copyright (C) 2026 AI.IMPACT GmbH
  SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.WellFoundedPart.Universe where

-- Restricted universe of “well-founded sets”: each base set carries `Acc _∈_`.

open import LogOS.Prelude
open import LogOS.LT.View using (μ)

import LogOS.Apps.ZFC.Stack.ProfileTower.Core as Tower
import LogOS.Apps.ZFC.Stack.ZFCore as ZF
import LogOS.Apps.ZFC.Stack.WellFounded as WF

module ForBase {ℓ : Level} (B : Tower.ZFStackBase {ℓ}) where
  open Tower.ZFStackBase B

  -- Constructor objects in the base universe.
  emptySet : SetU
  emptySet = μ EmptyV tt

  pairSet : SetU → SetU → SetU
  pairSet x y = μ PairV (x , y)

  unionSet : SetU → SetU
  unionSet x = μ UnionV x

  powersetSet : SetU → SetU
  powersetSet x = μ PowersetV x

  omegaSet : SetU
  omegaSet = μ OmegaV tt

  -- ----------------------------------------------------------------------
  -- Well-founded universe + induced membership.

  SetUᵂ : Set ℓ
  SetUᵂ = Σ SetU (λ x → WF.Acc _∈_ x)

  infix 4 _∈ᵂ_
  _∈ᵂ_ : SetUᵂ → SetUᵂ → Set ℓ
  u ∈ᵂ x = proj₁ u ∈ proj₁ x

  -- The restricted set context.
  ctxᵂ : ZF.SetContext {ℓ}
  ctxᵂ = record { SetU = SetUᵂ ; _∈_ = _∈ᵂ_ }

  -- Convenience: project/set constructors.
  ⌞_⌟ : SetUᵂ → SetU
  ⌞ x ⌟ = proj₁ x

  wf : (x : SetUᵂ) → WF.Acc _∈_ ⌞ x ⌟
  wf x = proj₂ x

  -- ----------------------------------------------------------------------
  -- Accessibility transport along extensional equality (≈).

  Acc-cong : ∀ {x y} → x ≈ y → WF.Acc _∈_ x → WF.Acc _∈_ y
  Acc-cong xy (WF.acc step) =
    WF.acc (λ z z∈y → step z (snd xy z z∈y))

  -- If `x` is accessible, then every member is accessible.
  wf-member : ∀ {x y} → WF.Acc _∈_ x → y ∈ x → WF.Acc _∈_ y
  wf-member {y = y} (WF.acc step) y∈x = step y y∈x
