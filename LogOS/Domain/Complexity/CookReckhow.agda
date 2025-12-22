{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.CookReckhow where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_; ⊥)

open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; fst; snd)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel
open import LogOS.Theorems.Meta.Base using (DeciderC; mkDeciderC)
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
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  (P : Kernel.Code K → Set ℓ)
  : Set (lsuc (lsuc ℓ)) where
  field
    core : PB.PolyBoundedSystem (Kernel.Code K) P

  open PB.PolyBoundedSystem core public

-- Core Cook–Reckhow lemma: a poly-bounded complete proof system yields a decider.

deciderFromProofSystem
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
    (P : Kernel.Code K → Set ℓ)
  → PolyBoundedProofSystem K P
  → DeciderC {K = K} P
deciderFromProofSystem P PS =
  mkDeciderC (PB.deciderFromPolyBoundedSystem P (PolyBoundedProofSystem.core PS))
