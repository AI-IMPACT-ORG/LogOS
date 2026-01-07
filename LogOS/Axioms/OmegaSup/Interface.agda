{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Axioms.OmegaSup.Interface where

open import LogOS.Prelude
open import Data.Nat using (ℕ)

open import LogOS.Minimal.Con
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Truth as Truth

-- This module is a **safe interface**: it introduces no global postulates.
-- This production snapshot ships no global ω-sup selector; supply `ChainSup`
-- explicitly to any model that needs ω-suprema.

record ChainSup {ℓ : Level} (CP : ConPoset ℓ) : Set (lsuc ℓ) where
  open ConPoset CP
  field
    supω  : (ℕ → Con) → Con
    ub    : ∀ (f : ℕ → Con) (n : ℕ) → _⊑_ (f n) (supω f)
    least : ∀ (f : ℕ → Con) (x : Con) → (∀ n → _⊑_ (f n) x) → _⊑_ (supω f) x

-- Build an OmegaCPO from a chosen ω-supremum operator and a provided bottom element.
omegaCPO-from-chainSup
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (CP : ConPoset ℓ)
    (bot : ConPoset.Con CP)
    (isBot : ∀ c → ConPoset._⊑_ CP bot c)
    (CS : ChainSup CP)
  → (let module GT = Truth.GuardedTruth Sig Q in GT.OmegaCPO) CP
omegaCPO-from-chainSup Sig Q CP bot isBot CS =
  let module GT = Truth.GuardedTruth Sig Q
      module CS' = ChainSup CS
      open ConPoset CP
  in
  record
    { ⊥     = bot
    ; isBot = isBot
    ; supω  = CS'.supω
    ; ub    = CS'.ub
    ; least = CS'.least
    }
