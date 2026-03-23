{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Sup.AbstractKleene where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Kleene-style least fixed point spine (μ) from σ-directed completeness.
--
-- This is an *optional* “tooling loop”:
-- if `f` is monotone and σ-continuous, then unrolling from bottom and taking a
-- σ-supremum yields a least fixed point up to mutual refinement (`≈`).

open import LogOS.Prelude
open import LogOS.Host.Nat using (ℕ; zero; suc)
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; _≈_; refl⊑)
open import LogOS.LT.Sup.FinSup using (HasBottom; PrefixPoint; PostfixPoint; FixedPoint≈)
open import LogOS.LT.Sup.AbstractSigmaDCPO using
  ( SigmaDCPO; Directedω; Chainω; chainDirectedω; mapDirectedω; SigmaContinuous )

module KleeneLocal
  {ℓCon ℓRel : Level}
  {CP : ConPreorder ℓCon ℓRel}
  (HB : HasBottom CP)
  (SD : SigmaDCPO CP)
  (f  : Con CP → Con CP)
  (fc : SigmaContinuous CP SD f)
  where
  open HasBottom HB
  open SigmaDCPO SD
  open SigmaContinuous fc
  module R = LogOS.Prelude.RefinementKit.Reasoning CP
  open R
  -- Iteration from bottom.
  iter⊥ : ℕ → Con CP
  iter⊥ zero    = ⊥ᵇ
  iter⊥ (suc n) = f (iter⊥ n)

  iter⊥-chain : Chainω {CP = CP} iter⊥
  iter⊥-chain zero    = ⊥ᵇ-least (f ⊥ᵇ)
  iter⊥-chain (suc n) = mono (iter⊥-chain n)

  iter⊥-dir : Directedω CP iter⊥
  iter⊥-dir = chainDirectedω {CP = CP} iter⊥ iter⊥-chain

  μ : Con CP
  μ = supσ iter⊥ iter⊥-dir

  -- Supremum of the tail of a chain is equivalent to the supremum of the chain.
  tail : (ℕ → Con CP) → ℕ → Con CP
  tail s n = s (suc n)

  tail-chain : ∀ {s} → Chainω {CP = CP} s → Chainω {CP = CP} (tail s)
  tail-chain step n = step (suc n)

  sup-tail≈
    : ∀ (s : ℕ → Con CP) (step : Chainω {CP = CP} s)
    → _≈_ CP
        (supσ s (chainDirectedω {CP = CP} s step))
        (supσ (tail s) (chainDirectedω {CP = CP} (tail s) (tail-chain step)))
  sup-tail≈ s step =
    ( sup≤tail , tail≤sup )
    where
      sup≤tail
        : _⊑_ CP
            (supσ s (chainDirectedω {CP = CP} s step))
            (supσ (tail s) (chainDirectedω {CP = CP} (tail s) (tail-chain step)))
      sup≤tail =
        leastσ s (chainDirectedω {CP = CP} s step) _ all≤tail
        where
          all≤tail : ∀ n → _⊑_ CP (s n) (supσ (tail s) (chainDirectedω {CP = CP} (tail s) (tail-chain step)))
          all≤tail zero =
            begin⊑
              s zero ⊑⟨ step zero ⟩
              s (suc zero) ⊑⟨ ubσ (tail s) (chainDirectedω {CP = CP} (tail s) (tail-chain step)) zero ⟩
              supσ (tail s) (chainDirectedω {CP = CP} (tail s) (tail-chain step)) ∎⊑
          all≤tail (suc n) = ubσ (tail s) (chainDirectedω {CP = CP} (tail s) (tail-chain step)) n

      tail≤sup
        : _⊑_ CP
            (supσ (tail s) (chainDirectedω {CP = CP} (tail s) (tail-chain step)))
            (supσ s (chainDirectedω {CP = CP} s step))
      tail≤sup =
        leastσ (tail s) (chainDirectedω {CP = CP} (tail s) (tail-chain step)) _ ubTail
        where
          ubTail : ∀ n → _⊑_ CP (tail s n) (supσ s (chainDirectedω {CP = CP} s step))
          ubTail n = ubσ s (chainDirectedω {CP = CP} s step) (suc n)

  supσ-unique≈
    : ∀ (s : ℕ → Con CP) (dir₁ dir₂ : Directedω CP s)
    → _≈_ CP (supσ s dir₁) (supσ s dir₂)
  supσ-unique≈ s dir₁ dir₂ =
    ( leastσ s dir₁ (supσ s dir₂) (λ n → ubσ s dir₂ n)
    , leastσ s dir₂ (supσ s dir₁) (λ n → ubσ s dir₁ n)
    )

  -- Fixed point property: μ is an f-fixed point (up to ≈) under σ-continuity.
  fμ≈μ : _≈_ CP (f μ) μ
  fμ≈μ =
    ( fμ≤μ , μ≤fμ )
    where
      contEq : _≈_ CP (f μ) (supσ (tail iter⊥) (mapDirectedω {CP = CP} mono iter⊥-dir))
      contEq = cont iter⊥ iter⊥-dir

      tailEq : _≈_ CP
        (supσ (tail iter⊥) (mapDirectedω {CP = CP} mono iter⊥-dir))
        (supσ (tail iter⊥) (chainDirectedω {CP = CP} (tail iter⊥) (tail-chain iter⊥-chain)))
      tailEq =
        supσ-unique≈
          (tail iter⊥)
          (mapDirectedω {CP = CP} mono iter⊥-dir)
          (chainDirectedω {CP = CP} (tail iter⊥) (tail-chain iter⊥-chain))

      μEq : _≈_ CP μ (supσ (tail iter⊥) (chainDirectedω {CP = CP} (tail iter⊥) (tail-chain iter⊥-chain)))
      μEq = sup-tail≈ iter⊥ iter⊥-chain

      fμ≤μ : _⊑_ CP (f μ) μ
      fμ≤μ =
        begin⊑
          f μ ⊑⟨ fst contEq ⟩
          (supσ (tail iter⊥) (mapDirectedω {CP = CP} mono iter⊥-dir))
            ⊑⟨ fst tailEq ⟩
          (supσ (tail iter⊥) (chainDirectedω {CP = CP} (tail iter⊥) (tail-chain iter⊥-chain)))
            ⊑⟨ snd μEq ⟩
          μ ∎⊑

      μ≤fμ : _⊑_ CP μ (f μ)
      μ≤fμ =
        begin⊑
          μ ⊑⟨ fst μEq ⟩
          (supσ (tail iter⊥) (chainDirectedω {CP = CP} (tail iter⊥) (tail-chain iter⊥-chain)))
            ⊑⟨ snd tailEq ⟩
          (supσ (tail iter⊥) (mapDirectedω {CP = CP} mono iter⊥-dir))
            ⊑⟨ snd contEq ⟩
          f μ ∎⊑

  μ-fix≈ : FixedPoint≈ CP f μ
  μ-fix≈ = fμ≈μ

  μ-prefix : PrefixPoint CP f μ
  μ-prefix = fst fμ≈μ

  μ-post : PostfixPoint CP f μ
  μ-post = snd fμ≈μ

  -- Least prefixpoint: any y with f y ⊑ y lies above μ.
  μ-leastPrefix
    : ∀ (y : Con CP)
    → _⊑_ CP (f y) y
    → _⊑_ CP μ y
  μ-leastPrefix y fy≤y =
    leastσ iter⊥ iter⊥-dir y iter≤y
    where
      iter≤y : ∀ n → _⊑_ CP (iter⊥ n) y
      iter≤y zero    = ⊥ᵇ-least y
      iter≤y (suc n) =
        begin⊑
          iter⊥ (suc n) ⊑⟨ mono (iter≤y n) ⟩
          f y ⊑⟨ fy≤y ⟩
          y ∎⊑

  -- Induction: to prove μ ⊑ y, it suffices to show y is a prefixpoint.
  μ-induction
    : ∀ (y : Con CP)
    → PrefixPoint CP f y
    → _⊑_ CP μ y
  μ-induction = μ-leastPrefix

  μ-leastFixed≈
    : ∀ (y : Con CP)
    → FixedPoint≈ CP f y
    → _⊑_ CP μ y
  μ-leastFixed≈ y fy≈y = μ-leastPrefix y (fst fy≈y)
