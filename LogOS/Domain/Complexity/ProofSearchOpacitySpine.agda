{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.ProofSearchOpacitySpine where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import Data.Nat using (ℕ)
open import Data.NatOrder using (_≤ℕ_)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel
open import LogOS.Theorems.Meta.Base using (NonTrivialC)

import LogOS.Domain.Complexity.ProofSearchBoundary as PBₜ
import LogOS.Theorems.Meta.SpectralSeparationOutput as SSOₜ
import LogOS.Theorems.Meta.BudgetedSeparationOutput as BSOₜ
open import LogOS.Theorems.Meta.Assumptions.Diagonal using (TruthDiagonalC)

-- Re-export the opacity/GRH core machinery for the PvsNP spine.
module SpectralSeparationOutput = SSOₜ
module BudgetedSeparationOutput = BSOₜ

-- Proof-search opacity spine: a proof-search oracle is a partial-output surface,
-- and the same diagonal/opacity machinery blocks any total, budget-bounded oracle.

module For {ℓ ℓP : Level}
           {Sig : LogOSSignature ℓ}
           {Q   : QAdapter ℓ}
           (K   : Kernel Sig Q)
           (P   : Kernel.Code K → Set ℓP)
           where

  open Kernel K using (Code; decode)

  module PB = PBₜ.For {ℓI = ℓ} {ℓ = ℓP} Code P

  open BSOₜ using (WitnessCost)

  ProofIndex : Set ℓ
  ProofIndex = Lift ℓ ℕ

  ProofCost : Set (lsuc ℓ)
  ProofCost = WitnessCost ProofIndex

  BudgetExt : (Code → ℕ) → Set ℓ
  BudgetExt Bnd = ∀ γ₁ γ₂ → decode γ₁ ≡ decode γ₂ → Bnd γ₁ ≡ Bnd γ₂

  record BudgetBy : Set (lsuc ℓ) where
    field
      budget : Code → ℕ
      ext    : BudgetExt budget

  -- A proof-search oracle: either return a proof code (with correctness) or abstain.
  -- Extensionality is decode-level (matches the GRH/opacity convention).
  record ProofSearchOracle (PS : PB.ProofSystem) : Set (lsuc (lsuc (ℓ ⊔ ℓP))) where
    field
      infer   : Code → ProofIndex ⊎ ⊤ {ℓ = lzero}
      ext     : ∀ γ₁ γ₂ → decode γ₁ ≡ decode γ₂ → infer γ₁ ≡ infer γ₂
      sound   : ∀ γ n → infer γ ≡ inj₁ n → PB.ProofSystem.Check PS (Lift.lower n) γ

  toSSO : ∀ {PS} → ProofSearchOracle PS → SSOₜ.SpectralSeparationOutput K
  toSSO O =
    record
      { core = record
          { Witness = ProofIndex
          ; infer   = ProofSearchOracle.infer O
          ; ext     = ProofSearchOracle.ext O
          }
      }

  -- Soundness: if the oracle returns a proof code, Prov∞ holds.
  oracle-sound
    : ∀ {PS} (O : ProofSearchOracle PS) (γ : Code)
      → SSOₜ.SpectralSeparationOutput.HasSeparation (toSSO O) γ
      → PB.Prov∞ PS γ
  oracle-sound O γ (n , eq) = Lift.lower n , ProofSearchOracle.sound O γ n eq

  module Budgeted {PS} (O : ProofSearchOracle PS) (C : ProofCost) where
    module B = BSOₜ.For (toSSO O) C
    infix 4 _≤B_
    _≤B_ : ProofIndex → ProofIndex → Set ℓ
    _≤B_ x y = Lift ℓ (Lift.lower x ≤ℕ Lift.lower y)

    module G = B.General ProofIndex _≤B_
      (record { costB = λ w → lift (WitnessCost.cost C w) })

    WithinBudget : (Code → ℕ) → Code → Set ℓ
    WithinBudget Bnd = G.WithinBudget (λ γ → lift (Bnd γ))

    no-total-within-budget
      : ∀ (Bnd : Code → ℕ)
        → TruthDiagonalC Code (WithinBudget Bnd)
        → ¬ (∀ γ → WithinBudget Bnd γ)
    no-total-within-budget Bnd TD =
      G.no-total-within-budget (λ γ → lift (Bnd γ)) TD

    diagonal-witness-within-budget
      : ∀ (Bnd : Code → ℕ)
        → TruthDiagonalC Code (WithinBudget Bnd)
        → Σ Code (λ γ → ¬ WithinBudget Bnd γ)
    diagonal-witness-within-budget Bnd TD =
      G.diagonal-witness-within-budget (λ γ → lift (Bnd γ)) TD

    WithinBudgetBy : BudgetBy → Code → Set ℓ
    WithinBudgetBy Bnd = WithinBudget (BudgetBy.budget Bnd)

    no-total-within-budgetBy
      : ∀ (Bnd : BudgetBy)
        → TruthDiagonalC Code (WithinBudgetBy Bnd)
        → ¬ (∀ γ → WithinBudgetBy Bnd γ)
    no-total-within-budgetBy Bnd TD =
      no-total-within-budget (BudgetBy.budget Bnd) TD

    diagonal-witness-within-budgetBy
      : ∀ (Bnd : BudgetBy)
        → TruthDiagonalC Code (WithinBudgetBy Bnd)
        → Σ Code (λ γ → ¬ WithinBudgetBy Bnd γ)
    diagonal-witness-within-budgetBy Bnd TD =
      diagonal-witness-within-budget (BudgetBy.budget Bnd) TD

    -- General budget carrier: keep the oracle/witness surface fixed, vary budgets.
    module GeneralB (Budget : Set ℓ)
                    (_≤B_ : Budget → Budget → Set ℓ)
                    (costB : ProofIndex → Budget)
                    where
      module GB = B.General Budget _≤B_ (record { costB = costB })

      WithinBudgetB : (Code → Budget) → Code → Set ℓ
      WithinBudgetB = GB.WithinBudget

      no-total-within-budgetB
        : ∀ (Bnd : Code → Budget)
          → TruthDiagonalC Code (WithinBudgetB Bnd)
          → ¬ (∀ γ → WithinBudgetB Bnd γ)
      no-total-within-budgetB = GB.no-total-within-budget

      diagonal-witness-within-budgetB
        : ∀ (Bnd : Code → Budget)
          → TruthDiagonalC Code (WithinBudgetB Bnd)
          → Σ Code (λ γ → ¬ WithinBudgetB Bnd γ)
      diagonal-witness-within-budgetB = GB.diagonal-witness-within-budget

  WithinBudget
    : ∀ {PS}
      → ProofSearchOracle PS
      → ProofCost
      → (Code → ℕ)
      → Code → Set ℓ
  WithinBudget O C Bnd =
    let module B = Budgeted O C in
    B.WithinBudget Bnd

  no-total-within-budget
    : ∀ {PS}
      → (O : ProofSearchOracle PS)
      → (C : ProofCost)
      → (Bnd : Code → ℕ)
      → TruthDiagonalC Code (WithinBudget O C Bnd)
      → ¬ (∀ γ → WithinBudget O C Bnd γ)
  no-total-within-budget O C Bnd TD =
    let module B = Budgeted O C in
    B.no-total-within-budget Bnd TD

  diagonal-witness-within-budget
    : ∀ {PS}
      → (O : ProofSearchOracle PS)
      → (C : ProofCost)
      → (Bnd : Code → ℕ)
      → TruthDiagonalC Code (WithinBudget O C Bnd)
      → Σ Code (λ γ → ¬ WithinBudget O C Bnd γ)
  diagonal-witness-within-budget O C Bnd TD =
    let module B = Budgeted O C in
    B.diagonal-witness-within-budget Bnd TD

  WithinBudgetBy
    : ∀ {PS}
      → ProofSearchOracle PS
      → ProofCost
      → BudgetBy
      → Code → Set ℓ
  WithinBudgetBy O C Bnd =
    let module B = Budgeted O C in
    B.WithinBudgetBy Bnd

  no-total-within-budgetBy
    : ∀ {PS}
      → (O : ProofSearchOracle PS)
      → (C : ProofCost)
      → (Bnd : BudgetBy)
      → TruthDiagonalC Code (WithinBudgetBy O C Bnd)
      → ¬ (∀ γ → WithinBudgetBy O C Bnd γ)
  no-total-within-budgetBy O C Bnd TD =
    let module B = Budgeted O C in
    B.no-total-within-budgetBy Bnd TD

  diagonal-witness-within-budgetBy
    : ∀ {PS}
      → (O : ProofSearchOracle PS)
      → (C : ProofCost)
      → (Bnd : BudgetBy)
      → TruthDiagonalC Code (WithinBudgetBy O C Bnd)
      → Σ Code (λ γ → ¬ WithinBudgetBy O C Bnd γ)
  diagonal-witness-within-budgetBy O C Bnd TD =
    let module B = Budgeted O C in
    B.diagonal-witness-within-budgetBy Bnd TD

  record VacuityGuards
    (PS : PB.ProofSystem)
    (O : ProofSearchOracle PS)
    (C : ProofCost)
    (Bnd : BudgetBy)
    : Set (lsuc (lsuc (ℓ ⊔ ℓP))) where
    field
      someWithin : Σ Code (λ γ → WithinBudgetBy O C Bnd γ)

  NonTrivialWithinBudget
    : ∀ {PS}
      → ProofSearchOracle PS
      → ProofCost
      → BudgetBy
      → Set ℓ
  NonTrivialWithinBudget O C Bnd =
    NonTrivialC {K = K} (WithinBudgetBy O C Bnd)

  -- Standard pack skeleton: assumptions and claim are self-contained.
  record Assumptions (PS : PB.ProofSystem) : Set (lsuc (lsuc (ℓ ⊔ ℓP))) where
    field
      oracle   : ProofSearchOracle PS
      cost     : ProofCost
      budget   : BudgetBy
      diagonal : TruthDiagonalC Code (WithinBudgetBy oracle cost budget)
      vacuity  : VacuityGuards PS oracle cost budget

  record Claim
    (PS : PB.ProofSystem)
    (O  : ProofSearchOracle PS)
    (C  : ProofCost)
    (Bnd : BudgetBy)
    : Set (lsuc (lsuc (ℓ ⊔ ℓP))) where
    field
      no-total : ¬ (∀ γ → WithinBudgetBy O C Bnd γ)
      witness  : Σ Code (λ γ → ¬ WithinBudgetBy O C Bnd γ)

  record Pack (PS : PB.ProofSystem) (A : Assumptions PS)
    : Set (lsuc (lsuc (ℓ ⊔ ℓP))) where
    field
      assumptions : Assumptions PS
      claim       : Claim PS (Assumptions.oracle A) (Assumptions.cost A) (Assumptions.budget A)
      nontrivial  : NonTrivialWithinBudget (Assumptions.oracle A) (Assumptions.cost A) (Assumptions.budget A)

  mkPack : ∀ {PS} → (A : Assumptions PS) → Pack PS A
  mkPack {PS} A =
    let noTotal =
          no-total-within-budgetBy
            (Assumptions.oracle A)
            (Assumptions.cost A)
            (Assumptions.budget A)
            (Assumptions.diagonal A)
        witness =
          diagonal-witness-within-budgetBy
            (Assumptions.oracle A)
            (Assumptions.cost A)
            (Assumptions.budget A)
            (Assumptions.diagonal A)
        claim =
          record
            { no-total = noTotal
            ; witness  = witness
            }
    in
    record
      { assumptions = A
      ; claim       = claim
      ; nontrivial  = VacuityGuards.someWithin (Assumptions.vacuity A) , witness
      }
