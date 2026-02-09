{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
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

-- Minimal building blocks: sometimes you only need “nonempty” (to prevent
-- vacuous ∀-implications) or “not-top” (to prevent tautological predicates).

record NonEmptyPred {ℓA ℓP : Level} (A : Set ℓA) (P : A → Set ℓP) : Set (ℓA ⊔ ℓP) where
  field
    witness : Σ A P

open NonEmptyPred public

record NotTopPred {ℓA ℓP : Level} (A : Set ℓA) (P : A → Set ℓP) : Set (ℓA ⊔ ℓP) where
  field
    counterexample : Σ A (λ a → ¬ P a)

open NotTopPred public

nonEmptyPred : ∀ {ℓA ℓP} {A : Set ℓA} {P : A → Set ℓP} → NontrivialPred A P → NonEmptyPred A P
nonEmptyPred nt = record { witness = NontrivialPred.trueWitness nt }

notTopPred : ∀ {ℓA ℓP} {A : Set ℓA} {P : A → Set ℓP} → NontrivialPred A P → NotTopPred A P
notTopPred nt = record { counterexample = NontrivialPred.falseWitness nt }

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

  at : NontrivialPred Con (Sat w)
  at =
    record
      { trueWitness  = c₀ , sat₀
      ; falseWitness = c₁ , unsat₁
      }

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
