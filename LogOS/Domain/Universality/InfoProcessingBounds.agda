{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Universality.InfoProcessingBounds where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import Data.Nat using (ℕ)
open import Data.NatOrder using (_≤ℕ_; z≤n; s≤s; trans≤ℕ) public

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter

open import LogOS.Domain.Universality.SecondLaw as SL
open import LogOS.Domain.Universality.LCUToLandauer as LCU

-- Local (safe) preorder on naturals, used only for throughput bounds
-- (shared via `Data.NatOrder`).

-- Information-processing bounds, LogOS-style:
-- we bound *irreversible* information loss per unit of physical time, while
-- keeping reversible computation fully alive.
--
-- Concretely:
-- - “irreversibility events” are abstracted as a natural-number measure `merges f`;
-- - a program has an associated physical time `ticks f : Time`; and
-- - there is a throughput budget `budget : Time → ℕ` such that merges f ≤ budget (ticks f).
--
-- Crucially, reversible/local-unitary programs are allowed to run for arbitrarily
-- long physical time while producing *zero* merges.

record ThroughputAssumptions {ℓ : Level}
                             (Sig : LogOSSignature ℓ)
                             (Q   : QAdapter ℓ)
                             : Set (lsuc (lsuc ℓ)) where
  open LogOSSignature Sig
  open QAdapter Q
  field
    -- 2nd-law/LCU base (provides LocalUnitary and the observable-level notion of merge)
    SL : SL.SecondLawAssumptions Sig Q

    -- Physical time assigned to a program.
    ticks : Cosp → Time

    -- A *count* of irreversible merge/erasure events performed by the program.
    merges : Cosp → ℕ

    -- Throughput budget: maximum number of merges allowed within a given time.
    budget : Time → ℕ

    merges≤budget : ∀ f → merges f ≤ℕ budget (ticks f)

    -- Reversible computation stays alive: local unitarity forces zero merges.
    unitary→merges0
      : ∀ f → LCUObsAssumptions.LocalUnitary (SL.SecondLawAssumptions.LCUA SL) f
            → merges f ≡ 0

-- Re-export `trans≤ℕ` from `Data.NatOrder`.
