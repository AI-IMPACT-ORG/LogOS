{-
  LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
  Copyright (C) 2026 AI.IMPACT GmbH
  SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.WellFoundedPart.Closure where

-- Closure of `Acc _∈_` under base constructors where derivable.
-- Any remaining closure obligations are tracked explicitly as data.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)

import LogOS.Apps.ZFC.Stack.ProfileTower.Core as Tower
import LogOS.Apps.ZFC.Stack.WellFounded as WF

import LogOS.Apps.ZFC.Stack.WellFoundedPart.Universe as Universe

module ForBase {ℓ : Level} (B : Tower.ZFStackBase {ℓ}) where
  open Tower.ZFStackBase B
  module U = Universe.ForBase B
  open U

  wf-empty : WF.Acc _∈_ emptySet
  wf-empty =
    WF.acc (λ y y∈e → ⊥-elim (empty-spec y y∈e))

  wf-pair : ∀ {x y} → WF.Acc _∈_ x → WF.Acc _∈_ y → WF.Acc _∈_ (pairSet x y)
  wf-pair {x} {y} wfx wfy =
    WF.acc step
    where
      step : ∀ z → z ∈ (pairSet x y) → WF.Acc _∈_ z
      step z z∈p with _↔_.to (pairing-spec x y z) z∈p
      ... | inj₁ z≈x = Acc-cong (sym≈ z≈x) wfx
      ... | inj₂ z≈y = Acc-cong (sym≈ z≈y) wfy

  wf-union : ∀ {x} → WF.Acc _∈_ x → WF.Acc _∈_ (unionSet x)
  wf-union {x} wfx =
    WF.acc
      (λ z z∈U →
        let (y , (y∈x , z∈y)) = _↔_.to (union-spec x z) z∈U in
        wf-member (wf-member wfx y∈x) z∈y
      )

  wf-powerset : ∀ {x} → WF.Acc _∈_ x → WF.Acc _∈_ (powersetSet x)
  wf-powerset {x} wfx =
    WF.acc
      (λ z z∈P →
        let inX = _↔_.to (powerset-spec x z) z∈P in
        WF.acc (λ w w∈z → wf-member wfx (inX w w∈z))
      )

  record BaseWFClosure : Set (lsuc ℓ) where
    field
      wfOmega : WF.Acc _∈_ omegaSet

  baseWFClosure
    : WF.Acc _∈_ omegaSet
    → BaseWFClosure
  baseWFClosure wfω = record { wfOmega = wfω }

  open BaseWFClosure public
