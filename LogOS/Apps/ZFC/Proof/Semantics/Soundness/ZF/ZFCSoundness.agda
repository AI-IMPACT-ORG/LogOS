{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Proof.Semantics.Soundness.ZF.ZFCSoundness where

open import LogOS.Prelude
open import LogOS.LT.View using (μ)

import LogOS.Apps.ZFC.Proof.Axioms as Ax
open Ax

import LogOS.Apps.ZFC.Proof.Semantics.Core as Core
import LogOS.Apps.ZFC.Proof.Semantics.Soundness.ZF.ZFSoundness as ZFSoundness

module ForModel {ℓ : Level} (M : Core.Model {ℓ}) where
  open Core.Model M
  open ZFSoundness.ForModel M public

  zfcSound : ∀ {ρ φ} → ZFCAxiom φ → evalFormula φ ρ
  zfcSound (axZF zfAx) = zfSound zfAx
  zfcSound {ρ} axChoice X nonempty =
    let
      f : SetU
      f = μ ChoiceV (X , nonempty)

      choiceLaw = choice-spec X nonempty
      dom = fst choiceLaw
      tot = fst (snd choiceLaw)
      fun = snd (snd choiceLaw)
    in
    f
      , ( ( dom
          , (λ x x∈X →
              let p = tot x x∈X
              in proj₁ p , proj₂ p)
          )
        , (λ x y₁ y₂ p₁ p₂ → fun x y₁ y₂ p₁ p₂)
        )
