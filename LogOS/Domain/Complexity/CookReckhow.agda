{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.CookReckhow where

open import LogOS.Prelude

open import LogOS.Computation.Decider using (Decider)
open import LogOS.Domain.Complexity.PolyBoundedCore as PB

-- Shared bounded search primitives.

import LogOS.Domain.Complexity.FiniteSearch as FS
open FS public using (Finℓ; toNat; fzero; fsuc)
module Search = FS.Search
open Search public using (ExistsFin; searchFin)

-- Cook–Reckhow style “NP via proofs”: a property P is in NP if there is a proof
-- system with decidable checking and a polynomial bound on proof *size*.
--
-- Here we model proofs by ℕ, and treat “size” as bounded by ≤ℕ directly.
-- This is enough to derive a *decider* for P by bounded search.

record PolyBoundedProofSystem
  {ℓI ℓ : Level}
  (Input : Set ℓI)
  (P : Input → Set ℓ)
  : Set (lsuc (lsuc (ℓ ⊔ ℓI))) where
  field
    core : PB.PolyBoundedSystem Input P

  open PB.PolyBoundedSystem core public

-- Core Cook–Reckhow lemma: a poly-bounded complete proof system yields a decider.

deciderFromProofSystem
  : ∀ {ℓI ℓ} {Input : Set ℓI}
    (P : Input → Set ℓ)
  → PolyBoundedProofSystem Input P
  → Decider Input P
deciderFromProofSystem P PS =
  PB.deciderFromPolyBoundedSystem P (PolyBoundedProofSystem.core PS)
