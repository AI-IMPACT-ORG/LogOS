{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.InfoProcessingBounds where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import LogOS.Prelude.Nat using (ℕ)
open import LogOS.Prelude.NatOrder using (_≤ℕ_; z≤n; s≤s; trans≤ℕ) public

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Ports.Semantic.SatMor using (SatRefinement₀; sat-→₀)

open import LogOS.Domain.Complexity.SecondLaw as SL
open import LogOS.Domain.Complexity.LCUToLandauer as LCU

-- Local (safe) preorder on naturals, used only for throughput bounds
-- (shared via `LogOS.Prelude.NatOrder`).

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

    -- Budget assumption as a refinement from trivial truth.
    budget-ref : SatRefinement₀ Cosp
                  (λ _ _ → ⊤ {ℓ = lzero})
                  (λ _ f → merges f ≤ℕ budget (ticks f))

    -- Reversible computation stays alive: local unitarity forces zero merges,
    -- expressed as a refinement between predicates.
    unitary-ref : SatRefinement₀ Cosp
                  (λ _ f → LCUObsAssumptions.LocalUnitary (SL.SecondLawAssumptions.LCUA SL) f)
                  (λ _ f → merges f ≡ 0)

  merges≤budget : ∀ f → merges f ≤ℕ budget (ticks f)
  merges≤budget f = sat-→₀ budget-ref f tt

  unitary→merges0
    : ∀ f → LCUObsAssumptions.LocalUnitary (SL.SecondLawAssumptions.LCUA SL) f
          → merges f ≡ 0
  unitary→merges0 f u = sat-→₀ unitary-ref f u

-- Re-export `trans≤ℕ` from `LogOS.Prelude.NatOrder`.
