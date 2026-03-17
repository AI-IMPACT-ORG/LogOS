{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Flow where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Normalisation doctrine (guarded closure on boundaries).
--
-- This is the order-theoretic “Flow” layer from the design-target spec:
-- a monotone, inflationary, lax-idempotent endomap on a boundary preorder
-- (a closure operator on a preorder, idempotent up to mutual refinement),
-- with no extra structure beyond the closure laws.
--
-- Polarity note:
-- `_⊑_ c d` means `d` is stronger than `c`. So `infl : c ⊑ Flow c` says
-- `Flow c` is the stronger/stabilised observation, and `idemp-lax` is
-- stabilization, not strict identity. When an order-like public-facing glyph
-- helps, read `c ≼ d` as this same refinement relation.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; _≈_; MonoOn; refl⊑)

record GuardedClosure {ℓCon ℓRel : Level} (CP : ConPreorder ℓCon ℓRel)
  : Set (lsuc (ℓCon ⊔ ℓRel)) where
  field
    Flow      : Con CP → Con CP
    mono      : MonoOn CP Flow
    infl      : ∀ c → _⊑_ CP c (Flow c)
    idemp-lax : ∀ c → _⊑_ CP (Flow (Flow c)) (Flow c)

open GuardedClosure public
-- Identity closure (a valid `GuardedClosure` for any boundary preorder).
idClosure : ∀ {ℓCon ℓRel} (CP : ConPreorder ℓCon ℓRel) → GuardedClosure CP
idClosure CP =
  record
    { Flow = λ c → c
    ; mono = λ le → le
    ; infl = λ _ → refl⊑ CP
    ; idemp-lax = λ _ → refl⊑ CP
    }

-- Stable points packaged as a record (prefixpoints: N x ⊑ x).
-- With the refinement polarity, this is the “postfixpoint/closed point” notion
-- in some order-theory conventions.
record Stable {ℓCon ℓRel : Level} {CP : ConPreorder ℓCon ℓRel} (N : Con CP → Con CP)
  : Set (lsuc (ℓCon ⊔ ℓRel)) where
  constructor mkStable
  field
    elem   : Con CP
    stable : _⊑_ CP (N elem) elem

open Stable public
-- --------------------------------------------------------------------------
-- Derived laws (no additional assumptions).
--
-- In order-theoretic literature, “closure operator” often includes strict
-- idempotence. LogOS keeps the primitive doctrine weak (lax-idempotent), but
-- mutual refinement (`≈`) idempotence is derivable:
--
--   Flow (Flow c) ≈ Flow c
--
-- Similarly, a stable point (prefixpoint) is a fixed point up to `≈`.

Flow-idemp≈
  : ∀ {ℓCon ℓRel : Level} {CP : ConPreorder ℓCon ℓRel}
  → (GC : GuardedClosure CP)
  → ∀ c → _≈_ CP (Flow GC (Flow GC c)) (Flow GC c)
Flow-idemp≈ GC c =
  ( idemp-lax GC c
  , infl GC (Flow GC c)
  )

Stable-fixpoint≈
  : ∀ {ℓCon ℓRel : Level} {CP : ConPreorder ℓCon ℓRel}
  → (GC : GuardedClosure CP)
  → (x : Stable {CP = CP} (Flow GC))
  → _≈_ CP (Flow GC (elem x)) (elem x)
Stable-fixpoint≈ GC x =
  ( stable x
  , infl GC (elem x)
  )
