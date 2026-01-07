{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.MonotonePredicates where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; to; from)
open import LogOS.Minimal.Con using (ConPoset)

-- Monotonicity for predicates over a preorder, and transport across pointwise ↔.
--
-- This is the predicate-level analogue of `MonoOn`/`MonoMap`: it shows that
-- “being monotone” is invariant under definitional reformulations of the
-- predicate, provided they are pointwise logically equivalent.

MonoPredOn
  : ∀ {ℓ ℓP}
    (CP : ConPoset ℓ)
    (P  : ConPoset.Con CP → Set ℓP)
  → Set (ℓ ⊔ ℓP)
MonoPredOn CP P = ∀ {c d} → ConPoset._⊑_ CP c d → P c → P d

AntiMonoPredOn
  : ∀ {ℓ ℓP}
    (CP : ConPoset ℓ)
    (P  : ConPoset.Con CP → Set ℓP)
  → Set (ℓ ⊔ ℓP)
AntiMonoPredOn CP P = ∀ {c d} → ConPoset._⊑_ CP c d → P d → P c

mapMonoPredOn
  : ∀ {ℓ ℓP}
    {CP : ConPoset ℓ}
    {P Q : ConPoset.Con CP → Set ℓP}
  → (∀ c → P c ↔ Q c)
  → MonoPredOn CP P
  → MonoPredOn CP Q
mapMonoPredOn {P = P} {Q = Q} eq mono {c} {d} c⊑d qc =
  to (eq d) (mono c⊑d (from (eq c) qc))

mapAntiMonoPredOn
  : ∀ {ℓ ℓP}
    {CP : ConPoset ℓ}
    {P Q : ConPoset.Con CP → Set ℓP}
  → (∀ c → P c ↔ Q c)
  → AntiMonoPredOn CP P
  → AntiMonoPredOn CP Q
mapAntiMonoPredOn {P = P} {Q = Q} eq anti {c} {d} c⊑d qd =
  to (eq c) (anti c⊑d (from (eq d) qd))
