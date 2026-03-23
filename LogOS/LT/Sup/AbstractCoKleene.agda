{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Sup.AbstractCoKleene where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Dual Kleene fixed-point spine (ν) via σ-directed completeness on `Opp`.

open import LogOS.Prelude
open import LogOS.Host.Nat using (ℕ; zero; suc)
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; _≈_; Opp)
open import LogOS.LT.Sup.FinSup using (HasTop; HasBottom; hasBottomOppFromHasTop; FixedPoint≈; PrefixPoint; PostfixPoint)
open import LogOS.LT.Sup.AbstractSigmaDCPO using (SigmaDCPO; SigmaContinuous)
import LogOS.LT.Sup.AbstractKleene as Kleene

SigmaCoContinuous
  : ∀ {ℓCon ℓRel : Level}
  → (CP : ConPreorder ℓCon ℓRel)
  → SigmaDCPO (Opp CP)
  → (Con CP → Con CP)
  → Set (lsuc (ℓCon ⊔ ℓRel))
SigmaCoContinuous CP SDᵒᵖ f = SigmaContinuous (Opp CP) SDᵒᵖ f

module CoKleeneLocal
  {ℓCon ℓRel : Level}
  {CP : ConPreorder ℓCon ℓRel}
  (HT : HasTop CP)
  (SDᵒᵖ : SigmaDCPO (Opp CP))
  (f  : Con CP → Con CP)
  (fc : SigmaCoContinuous CP SDᵒᵖ f)
  where

  private
    HBᵒᵖ : HasBottom (Opp CP)
    HBᵒᵖ = hasBottomOppFromHasTop {CP = CP} HT

  module K = Kleene.KleeneLocal {CP = Opp CP} HBᵒᵖ SDᵒᵖ f fc

  -- Iteration from top (in `CP`) is Kleene iteration from bottom in `Opp CP`.
  iter⊤ : ℕ → Con CP
  iter⊤ = K.iter⊥

  -- Greatest fixed point (ν) of `f` under σ-co-continuity.
  ν : Con CP
  ν = K.μ

  -- Fixed point property (up to mutual refinement).
  fν≈ν : _≈_ CP (f ν) ν
  fν≈ν = (snd K.fμ≈μ , fst K.fμ≈μ)

  ν-fix≈ : FixedPoint≈ CP f ν
  ν-fix≈ = fν≈ν

  ν-prefix : PrefixPoint CP f ν
  ν-prefix = fst fν≈ν

  ν-post : PostfixPoint CP f ν
  ν-post = snd fν≈ν

  -- Greatest postfixpoint: any y with y ⊑ f y lies below ν.
  ν-greatestPost
    : ∀ (y : Con CP)
    → _⊑_ CP y (f y)
    → _⊑_ CP y ν
  ν-greatestPost y y≤fy = K.μ-leastPrefix y y≤fy

  -- Coinduction: to prove y ⊑ ν, it suffices to show y is a postfixpoint.
  ν-coinduction
    : ∀ (y : Con CP)
    → PostfixPoint CP f y
    → _⊑_ CP y ν
  ν-coinduction = ν-greatestPost

  ν-greatestFixed≈
    : ∀ (y : Con CP)
    → FixedPoint≈ CP f y
    → _⊑_ CP y ν
  ν-greatestFixed≈ y fy≈y = ν-greatestPost y (snd fy≈y)
