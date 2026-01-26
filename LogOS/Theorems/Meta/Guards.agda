{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.Guards where

-- Small, reusable “nontriviality / nonvacuity” witnesses used across the library.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)
open import LogOS.Minimal.Con using (ConPreorder; TopOrder)

-- A predicate is nontrivial if it has both a satisfying and a refuting witness.

record NontrivialPred {ℓA ℓP : Level} (A : Set ℓA) (P : A → Set ℓP) : Set (ℓA ⊔ ℓP) where
  field
    trueWitness  : Σ A P
    falseWitness : Σ A (λ a → ¬ P a)

open NontrivialPred public

-- A set is nontrivial if it has at least two provably distinct inhabitants.
--
-- This is a useful “anti-vacuity” input when a code/interface can collapse to a
-- singleton (making many existence claims tautological).

record NontrivialSet {ℓ : Level} (A : Set ℓ) : Set (lsuc ℓ) where
  field
    a₀ a₁ : A
    a₀≠a₁ : ¬ (a₀ ≡ a₁)

open NontrivialSet public

-- A satisfaction relation is nonvacuous if it distinguishes at least two constraints
-- in some world.

record NonVacuousSat
  {ℓW ℓC ℓS : Level}
  (World : Set ℓW)
  (Con   : Set ℓC)
  (Sat   : World → Con → Set ℓS)
  : Set (ℓW ⊔ ℓC ⊔ ℓS) where
  field
    w   : World
    c₀ c₁ : Con
    sat₀  : Sat w c₀
    unsat₁ : ¬ (Sat w c₁)

open NonVacuousSat public

-- Cross-cutting “meaningfulness bundle” for kernel-driven readings:
-- - boundary order is not the top preorder,
-- - satisfaction is nonvacuous somewhere,
-- - the code/interface is nontrivial.
--
-- This is intentionally generic: many concrete ledgers (GRH, P/NP, opacity,
-- observer semantics) can be instantiated vacuously without additional guards.

record MeaningfulnessBundle
  {ℓW ℓC ℓS ℓCode : Level}
  (CP    : ConPreorder ℓC)
  (World : Set ℓW)
  (Sat   : World → ConPreorder.Con CP → Set ℓS)
  (Code  : Set ℓCode)
  : Set (lsuc (ℓW ⊔ ℓC ⊔ ℓS ⊔ ℓCode)) where
  field
    order-not-top : ¬ (TopOrder CP)
    sat-nonvacuous : NonVacuousSat World (ConPreorder.Con CP) Sat
    code-nontrivial : NontrivialSet Code

open MeaningfulnessBundle public
