{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Prelude where

-- ============================================================================
-- LogOS PRELUDE
-- Curated foundation layer for the LogOS logic system.
-- Provides common imports in one place.
--
-- This prelude curates common foundational imports in one place. It
-- re-exports a minimal set of levels, equality, and data combinators used
-- across the library (stdlib-independent via `LogOS.Host.*`).
--
-- Prefer importing via `LogOS.API.Minimal` / `LogOS.API.Architecture` to avoid
-- name clashes (or fully qualify imports).
-- ============================================================================

-- Foundation: Level polymorphism
open import LogOS.Host.Level public

-- Equality: Propositional equality
open import LogOS.Host.Relation.Binary.PropositionalEquality public

-- Data types: Core algebraic structures
open import LogOS.Host.Nat public
open import LogOS.Host.Sum public
open import LogOS.Host.Product public
-- NOTE: we intentionally do not re-export `⊥` from the global Prelude, because
-- many order-/algebra-structures use `⊥` as a bottom element field name.
-- Import `LogOS.Prelude.Empty` (or `LogOS.Host.Empty`) explicitly when needed.
open import LogOS.Prelude.Empty using (⊥)

-- Universe-polymorphic unit type at arbitrary level ℓ
data Topℓ {ℓ : Level} : Set ℓ where
  ttℓ : Topℓ

-- Minimal truth / unit, avoiding Agda.Builtin.Unit.
--
-- Keep the conventional names `⊤` and `tt` available at all universe levels.
⊤ : ∀ {ℓ : Level} → Set ℓ
⊤ {ℓ} = Topℓ {ℓ = ℓ}

tt : ∀ {ℓ : Level} → ⊤ {ℓ}
tt {ℓ} = ttℓ

-- Negation (using the canonical empty type from `LogOS.Host.Empty`).
infix 6 ¬_
¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬_ {ℓ} P = P → ⊥ {lzero}
