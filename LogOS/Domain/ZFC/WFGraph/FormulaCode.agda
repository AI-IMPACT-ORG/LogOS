{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.ZFC.WFGraph.FormulaCode where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (⊥)

open import LogOS.Prelude.Fin using (Fin)
open import LogOS.Prelude.Product using (Σ; _,_; _×_)

open import LogOS.ObjectLogic.FOL.Syntax as FOL using (Signature; Fml)

-- Pure first-order *set theory* signature: just membership and equality.
-- There are no predicate symbols; formulas are purely relational.

data STRel₂ {ℓ : Level} : Set ℓ where
  mem : STRel₂
  eq  : STRel₂

ΣST : ∀ {ℓ : Level} → Signature {ℓ}
ΣST {ℓ} = record
  { PredSym = ⊥ {ℓ}
  ; RelSym₂ = STRel₂ {ℓ}
  }

-- “Formula codes” for the ZF schemata are formulas with explicit parameters.
--
-- A predicate code has one distinguished free variable (the element being tested),
-- plus `k` parameters stored as values in the ambient set universe.
--
-- A relation code has two distinguished free variables (input/output), plus `k`
-- parameters.
--
-- Parameter arity is stored explicitly as a `k : ℕ` so we can build the matching
-- environment without doing list-to-Fin conversions.

PredCode : ∀ {ℓ : Level} (SetU : Set ℓ) → Set ℓ
PredCode {ℓ} SetU =
  Σ ℕ (λ k → (Fin k → SetU) × (Fml (ΣST {ℓ}) (suc k)))

RelCode : ∀ {ℓ : Level} (SetU : Set ℓ) → Set ℓ
RelCode {ℓ} SetU =
  Σ ℕ (λ k → (Fin k → SetU) × (Fml (ΣST {ℓ}) (suc (suc k))))
