{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Sup.AbstractSigmaDCPO where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- σ-directed ω-suprema (σ-dcpo structure) and continuity.
--
-- This is the “infinitary but localised” half of the optional completeness
-- layer: suprema only for *directed* ω-families (ℕ-indexed families).
--
-- It also provides a small amount of infrastructure used by derived `supω`
-- and the Kleene μ/ν fixed-point spines.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using
  ( ConPreorder; Con; _⊑_; _≈_; refl⊑; MonoOn; Opp )
open import LogOS.LT.Stage.SuccessorChain using
  ( Stageω; zero; suc; _≤ω_; z≤ω; s≤ω; ≤ω-maxL; ≤ω-maxR; maxω )

Directedω
  : ∀ {ℓCon ℓRel : Level}
  → (CP : ConPreorder ℓCon ℓRel)
  → (Stageω → Con CP)
  → Set ℓRel
Directedω CP s =
  ∀ i j → Σ Stageω (λ k → (_⊑_ CP (s i) (s k)) × (_⊑_ CP (s j) (s k)))

record SigmaDCPO {ℓCon ℓRel : Level} (CP : ConPreorder ℓCon ℓRel) : Set (lsuc (ℓCon ⊔ ℓRel)) where
  field
    supσ : (s : Stageω → Con CP) → Directedω CP s → Con CP

    ubσ
      : ∀ (s : Stageω → Con CP) (dir : Directedω CP s) (n : Stageω)
      → _⊑_ CP (s n) (supσ s dir)

    leastσ
      : ∀ (s : Stageω → Con CP) (dir : Directedω CP s) (x : Con CP)
      → (∀ n → _⊑_ CP (s n) x)
      → _⊑_ CP (supσ s dir) x

-- Directedness is preserved by monotone maps.
mapDirectedω
  : ∀ {ℓCon ℓRel : Level} {CP : ConPreorder ℓCon ℓRel}
    {f : Con CP → Con CP}
  → MonoOn CP f
  → ∀ {s : Stageω → Con CP}
  → Directedω CP s
  → Directedω CP (λ n → f (s n))
mapDirectedω {CP = CP} monoF dir i j with dir i j
... | k , (si≤sk , sj≤sk) = k , (monoF si≤sk , monoF sj≤sk)

-- σ-continuity (directed ω-suprema) for endomaps: preserve `supσ`.
--
-- Terminology note: in classical domain theory, “Scott-continuous” usually
-- means preservation of *all* directed suprema. LogOS keeps only the σ/ω
-- fragment explicit (`Directedω`).
record SigmaContinuous
  {ℓCon ℓRel : Level}
  (CP : ConPreorder ℓCon ℓRel)
  (SD : SigmaDCPO CP)
  (f : Con CP → Con CP)
  : Set (lsuc (ℓCon ⊔ ℓRel)) where
  field
    mono : MonoOn CP f
    cont
      : ∀ (s : Stageω → Con CP) (dir : Directedω CP s)
      → _≈_ CP
          (f (SigmaDCPO.supσ SD s dir))
          (SigmaDCPO.supσ SD (λ n → f (s n)) (mapDirectedω {CP = CP} mono dir))

-- --------------------------------------------------------------------------
-- ω-chains and a constructive “chain implies directed” lemma.

-- ω-chains (successor monotone sequences).
Chainω : ∀ {ℓCon ℓRel : Level} {CP : ConPreorder ℓCon ℓRel} → (Stageω → Con CP) → Set ℓRel
Chainω {CP = CP} s = ∀ n → _⊑_ CP (s n) (s (suc n))

private
  chain-mono
    : ∀ {ℓCon ℓRel : Level} {CP : ConPreorder ℓCon ℓRel}
    → (s : Stageω → Con CP)
    → Chainω {CP = CP} s
    → ∀ {m n} → m ≤ω n → _⊑_ CP (s m) (s n)
  chain-mono {CP = CP} s step {n = n} z≤ω = go n
    where
      module R = LogOS.Prelude.RefinementKit.Reasoning CP
      open R
      go : ∀ n -> _⊑_ CP (s zero) (s n)
      go zero    = refl⊑ CP
      go (suc n) =
        begin⊑
          s zero ⊑⟨ go n ⟩
          s n ⊑⟨ step n ⟩
          s (suc n) ∎⊑
  chain-mono {CP = CP} s step {m = suc m} {n = suc n} (s≤ω mn) =
    chain-mono {CP = CP} (λ k → s (suc k)) (λ k → step (suc k)) mn

-- ω-chains are directed (constructively: use `max` as a join on indices).
chainDirectedω
  : ∀ {ℓCon ℓRel : Level} {CP : ConPreorder ℓCon ℓRel}
  → (s : Stageω → Con CP)
  → Chainω {CP = CP} s
  → Directedω CP s
chainDirectedω {CP = CP} s step i j =
  let k = maxω i j in
  k , ( chain-mono {CP = CP} s step (≤ω-maxL i j)
      , chain-mono {CP = CP} s step (≤ω-maxR i j)
      )
