{-
LogOS: an Agda research library for foundational logic system architecture.
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
-- This prelude curates common stdlib imports in one place. It re-exports a
-- minimal set of levels, equality, and data combinators used across the
-- library. Prefer importing via `LogOS.API.Minimal` to avoid name clashes
-- (or fully qualify imports).
-- ============================================================================

-- Foundation: Level polymorphism
open import Host.Level public

-- Equality: Propositional equality
open import Data.Relation.Binary.PropositionalEquality public

-- Data types: Core algebraic structures
open import Data.Nat public
open import Data.Sum public
open import Data.Product public

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
