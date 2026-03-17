{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Prelude where

-- Minimal, stdlib-independent prelude for LogOS v1.1.
--
-- ============================================================================
-- LogOS 1.1 PRELUDE (minimal)
--
-- A minimal, stdlib-independent base layer:
-- - levels + Lift
-- - propositional equality
-- - Σ / × / ⊎
-- - ⊥ / ¬_ / ⊤
--
-- Higher layers should avoid importing Agda builtins directly; keep those in
-- `LogOS.Host.*`.
-- ============================================================================

open import LogOS.Host.Level public
open import LogOS.Host.Relation.Binary.PropositionalEquality public
open import LogOS.Host.Nat public
open import LogOS.Host.Sum public
open import LogOS.Host.Product public
open import LogOS.Host.Empty public

-- Canonical refinement preorder kit (kept separate to avoid polluting the base
-- namespace with generic names like `Con`/`_⊑_`).
open import LogOS.Prelude.Refinement public using (Refinement)

-- Full refinement kit (relations, derived `≈`, monotonicity helpers, ...),
-- namespaced to avoid collisions with the rest of the prelude.
module RefinementKit where
  open import LogOS.Prelude.Refinement public
-- Universe-polymorphic unit type at arbitrary level ℓ.
data Topℓ {ℓ : Level} : Set ℓ where
  ttℓ : Topℓ

⊤ : ∀ {ℓ : Level} → Set ℓ
⊤ {ℓ} = Topℓ {ℓ = ℓ}

tt : ∀ {ℓ : Level} → ⊤ {ℓ}
tt {ℓ} = ttℓ

infix 6 ¬_
¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬_ {ℓ} P = P → ⊥ {lzero}
