{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Safety.NoTotalAuditor where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_; to)

-- Reuse the existing opacity/diagonal machinery wholesale:
-- “no total auditor within budget” is a repackaging of `BudgetedSeparationOutput`.

open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (inj₁)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)

import LogOS.Computation.SchemeCategory as Cat

open import LogOS.Theorems.Meta.Assumptions.Diagonal using (TruthDiagonalC)

import LogOS.Packs.Agents.Safety.Audit as Audit
open import LogOS.Packs.Agents.Socket.Core using (AgentSocket)

-- Generic budget-form impossibility theorem: any decode-extensional auditor
-- cannot be total within an arbitrary budget discipline, assuming diagonal
-- representability for the “within-budget” predicate.

module ForProcess
  {ℓO ℓC ℓQ : Level}
  {Output : Set ℓO}
  (P : Cat.Process {ℓO = ℓO} {ℓC = ℓC} {ℓQ = ℓQ} Output)
  where

  module A = Audit.ForProcess P
  open A using (Auditor)

  module G = A.G
  open Cat.Process P using (Con; decode)

  toSSO : Auditor → G.SpectralSeparationOutputC
  toSSO = A.Auditor.core

  -- If you provide diagonalization for the “has separation” predicate induced
  -- by the auditor, you get a concrete counterexample to *total* auditing.
  no-total-auditor
    : (Aud : Auditor)
      → TruthDiagonalC Con (G.SpectralSeparationOutputC.HasSeparation (toSSO Aud))
      → ¬ (∀ s → G.SpectralSeparationOutputC.HasSeparation (toSSO Aud) s)
  no-total-auditor Aud TD =
    G.separation-output-not-totalC (toSSO Aud) TD

  -- Budget interface: equip witnesses with a cost/size and define “observable
  -- within budget” as an explicit predicate (no decidable order required).
  record WitnessCost (Witness : Set ℓC) : Set (lsuc ℓC) where
    field
      cost : Witness → ℕ

  module GeneralBudget (Aud : Auditor) where
    open A.Auditor Aud

    record WitnessCostB (B : Set ℓC) : Set (lsuc ℓC) where
      field
        costB : Witness → B

    module General
      (B : Set ℓC)
      (_≤B_ : B → B → Set ℓC)
      (CB : WitnessCostB B)
      where

      open WitnessCostB CB using (costB)

      WithinBudget
        : (Bnd : Con → B)
        → Con → Set ℓC
      WithinBudget Bnd s =
        Σ Witness (λ w → infer s ≡ inj₁ w × costB w ≤B Bnd s)

      no-total-within-budget
        : (Bnd : Con → B)
          → TruthDiagonalC Con (WithinBudget Bnd)
          → ¬ (∀ s → WithinBudget Bnd s)
      no-total-within-budget Bnd TD all =
        let liar = TruthDiagonalC.liarForDecider TD (λ _ → ⊤) (λ _ → inj₁ tt)
            s    = proj₁ liar
            eqv  = proj₂ liar
            ws   = all s
        in to eqv ws tt

module ForSocket
  {ℓ ℓTask : Level}
  {Sig  : LogOSSignature ℓ}
  {Q    : QAdapter ℓ}
  {Task : Set ℓTask}
  (S : AgentSocket Sig Q Task)
  where

  module P = ForProcess (AgentSocket.P S)
  open P public

-- Optional: the proof-search opacity spine is a ready-made instantiation of
-- “auditing as a partial-output surface”, packaged for proof systems.
--
-- We re-export it here as a recommended downstream instance, without changing
-- any of its statements.
import LogOS.Packs.Complexity.ProofSearchOpacitySpine as ProofSearchOpacitySpineₜ
module ProofSearchOpacity = ProofSearchOpacitySpineₜ
