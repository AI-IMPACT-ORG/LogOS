{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.ConPreorder.Truth where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Propositions as a refinement preorder.
--
-- `TruthPreorder` orders propositions by *implication*:
--
--   P ⊑ Q  :⇔  (P → Q)
--
-- This is convenient for proof theory / semantic consequence (where refinement is
-- literally entailment).
--
-- Important polarity note (LogOS convention for *boundaries*):
-- the core refinement reading is “right side is stronger” (`c ⊑ d` means “d entails c”).
-- For propositions, that boundary polarity is *reverse implication*.
--
-- Use `TruthBoundary = Opp TruthPreorder` when you want to treat propositions as
-- boundary constraints aligned with `Contracts` (where satisfaction is `c ⊑ decode γ`).

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Opp)
open import LogOS.LT.View using (View)

TruthPreorder : ∀ {ℓ : Level} → ConPreorder (lsuc ℓ) ℓ
TruthPreorder {ℓ} =
  record
    { Con   = Set ℓ
    ; _⊑_   = λ P Q → P → Q
    ; refl  = λ p → p
    ; trans = λ pq qr p → qr (pq p)
    }

-- Propositions as a *boundary* preorder in the LogOS refinement polarity
-- (reverse implication: `P ⊑ Q` means `Q → P`).
TruthBoundary : ∀ {ℓ : Level} → ConPreorder (lsuc ℓ) ℓ
TruthBoundary {ℓ} = Opp (TruthPreorder {ℓ})

truthView
  : ∀ {ℓX ℓ : Level} {X : Set ℓX}
  → (X → Set ℓ)
  → View X (TruthPreorder {ℓ})
truthView eval = record { μ = eval }

truthBoundaryView
  : ∀ {ℓX ℓ : Level} {X : Set ℓX}
  → (X → Set ℓ)
  → View X (TruthBoundary {ℓ})
truthBoundaryView eval = record { μ = eval }
