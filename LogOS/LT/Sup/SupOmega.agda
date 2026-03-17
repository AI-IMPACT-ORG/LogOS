{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Sup.SupOmega where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Derived: ω-joins `supω` from (FinSup + SigmaDCPO).
--
-- The key move: for an arbitrary sequence `s`, take finite prefix joins to get
-- an ω-chain, observe that any ω-chain is directed, and then take a σ-supremum.
--
-- This isolates the infinitary assumption to the σ-directed case, while still
-- supporting “iteration summaries” (e.g. `LogOS.LT.Iteration.run`).

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; refl⊑)
open import LogOS.LT.Sup.FinSup using (FinSup)
open import LogOS.LT.Sup.AbstractSigmaDCPO using (SigmaDCPO; Chainω; chainDirectedω)

module SupOmegaSection {ℓCon ℓRel : Level} {CP : ConPreorder ℓCon ℓRel} (FS : FinSup CP) (SD : SigmaDCPO CP) where
  open FinSup FS
  open SigmaDCPO SD
  module R = LogOS.Prelude.RefinementKit.Reasoning CP
  open R
  -- Finite prefix-joins of a sequence.
  prefix⊔ : (ℕ → Con CP) → ℕ → Con CP
  prefix⊔ s zero    = s zero
  prefix⊔ s (suc n) = prefix⊔ s n ⊔ᶠ s (suc n)

  prefix-step : ∀ s → Chainω {CP = CP} (prefix⊔ s)
  prefix-step s n = ⊔ᶠ-ub₁ (prefix⊔ s n) (s (suc n))

  prefix-directed : ∀ s → LogOS.LT.Sup.AbstractSigmaDCPO.Directedω CP (prefix⊔ s)
  prefix-directed s = chainDirectedω {CP = CP} (prefix⊔ s) (prefix-step s)

  -- `s n` is always below its own prefix-join.
  s≤prefix : ∀ s n → _⊑_ CP (s n) (prefix⊔ s n)
  s≤prefix s zero    = refl⊑ CP
  s≤prefix s (suc n) = ⊔ᶠ-ub₂ (prefix⊔ s n) (s (suc n))

  -- The derived ω-supremum of an arbitrary sequence.
  supω : (ℕ → Con CP) → Con CP
  supω s = supσ (prefix⊔ s) (prefix-directed s)

  ubω : ∀ s n → _⊑_ CP (s n) (supω s)
  ubω s n =
    begin⊑
      s n ⊑⟨ s≤prefix s n ⟩
      prefix⊔ s n ⊑⟨ ubσ (prefix⊔ s) (prefix-directed s) n ⟩
      supω s ∎⊑

  leastω
    : ∀ (s : ℕ → Con CP) (x : Con CP)
    → (∀ n → _⊑_ CP (s n) x)
    → _⊑_ CP (supω s) x
  leastω s x s≤x =
    leastσ (prefix⊔ s) (prefix-directed s) x prefix≤x
    where
      prefix≤x : ∀ n → _⊑_ CP (prefix⊔ s n) x
      prefix≤x zero    = s≤x zero
      prefix≤x (suc n) = ⊔ᶠ-least (prefix≤x n) (s≤x (suc n))
