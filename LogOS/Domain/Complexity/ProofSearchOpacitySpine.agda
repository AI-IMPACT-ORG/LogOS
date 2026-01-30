{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.ProofSearchOpacitySpine where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import LogOS.Prelude.Nat using (ℕ)
open import LogOS.Prelude.NatOrder using (_≤ℕ_)
open import LogOS.Prelude.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import LogOS.Prelude.Sum using (_⊎_; inj₁; inj₂)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel
open import LogOS.Theorems.Meta.Base using (NonTrivialC)

import LogOS.Domain.Complexity.ProofSearchBoundary as PBₜ
import LogOS.Theorems.Meta.SpectralSeparationOutput as SSOₜ
import LogOS.Theorems.Meta.BudgetedSeparationOutput as BSOₜ
open import LogOS.Theorems.Meta.Assumptions.Diagonal using (TruthDiagonalC)
import LogOS.Theorems.Meta.ApplicationKit as AppKit
open import LogOS.Theorems.Meta.Assumptions.Core using (DecodeExtensionalFn≈)

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
  BudgetExt = DecodeExtensionalFn≈ K

  record BudgetBy : Set (lsuc ℓ) where
    field
      budget : Code → ℕ
      ext    : BudgetExt budget

  -- A proof-search oracle: either return a proof code (with correctness) or abstain.
  -- Extensionality is decode-level up to decoded mutual refinement,
  -- matching the GRH/opacity convention.
  record ProofSearchOracle (PS : PB.ProofSystem) : Set (lsuc (lsuc (ℓ ⊔ ℓP))) where
    field
      oracle : SSOₜ.Oracle K ProofIndex
      sound  : ∀ γ n →
        SSOₜ.Oracle.infer oracle γ ≡ inj₁ n → PB.ProofSystem.Check PS (Lift.lower n) γ

    open SSOₜ.Oracle oracle public using (infer; ext)

  toSSO : ∀ {PS} → ProofSearchOracle PS → SSOₜ.SpectralSeparationOutput K
  toSSO O = SSOₜ.Oracle.toSSO (ProofSearchOracle.oracle O)

  -- Soundness: if the oracle returns a proof code, Prov∞ holds.
  oracle-sound
    : ∀ {PS} (O : ProofSearchOracle PS) (γ : Code)
      → SSOₜ.SpectralSeparationOutput.HasSeparation (toSSO O) γ
      → PB.Prov∞ PS γ
  oracle-sound O γ (n , eq) = Lift.lower n , ProofSearchOracle.sound O γ n eq

  module Budgeted {PS} (O : ProofSearchOracle PS) (C : ProofCost) where
    module OG = SSOₜ.GeneralB (toSSO O)
    infix 4 _≤B_
    _≤B_ : ProofIndex → ProofIndex → Set ℓ
    _≤B_ x y = Lift ℓ (Lift.lower x ≤ℕ Lift.lower y)

    module G = OG.General ProofIndex _≤B_
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
    open OG public using (WitnessCostB)
    module General = OG.General

  record VacuityGuards
    (PS : PB.ProofSystem)
    (O : ProofSearchOracle PS)
    (C : ProofCost)
    (Bnd : BudgetBy)
    : Set (lsuc (lsuc (ℓ ⊔ ℓP))) where
    private
      module B = Budgeted O C
    field
      someWithin : Σ Code (λ γ → B.WithinBudgetBy Bnd γ)

  NonTrivialWithinBudget
    : ∀ {PS}
      → ProofSearchOracle PS
      → ProofCost
      → BudgetBy
      → Set ℓ
  NonTrivialWithinBudget O C Bnd =
    let module B = Budgeted O C in
    NonTrivialC {K = K} (B.WithinBudgetBy Bnd)

  -- Standard pack skeleton: assumptions and claim are self-contained.
  record Assumptions (PS : PB.ProofSystem) : Set (lsuc (lsuc (ℓ ⊔ ℓP))) where
    field
      oracle   : ProofSearchOracle PS
      cost     : ProofCost
      budget   : BudgetBy
      diagonal : let module B = Budgeted oracle cost in
                 TruthDiagonalC Code (B.WithinBudgetBy budget)
      vacuity  : VacuityGuards PS oracle cost budget

  record Claim (PS : PB.ProofSystem) (A : Assumptions PS) : Set (lsuc (lsuc (ℓ ⊔ ℓP))) where
    open Assumptions A
    private
      module B = Budgeted oracle cost
    field
      no-total : ¬ (∀ γ → B.WithinBudgetBy budget γ)
      witness  : Σ Code (λ γ → ¬ B.WithinBudgetBy budget γ)
      nontrivial : NonTrivialWithinBudget oracle cost budget

  derive : ∀ {PS} (A : Assumptions PS) → Claim PS A
  derive A =
    let
      module B = Budgeted (Assumptions.oracle A) (Assumptions.cost A)
      noTotal =
        B.no-total-within-budgetBy
          (Assumptions.budget A)
          (Assumptions.diagonal A)
      witness =
        B.diagonal-witness-within-budgetBy
          (Assumptions.budget A)
          (Assumptions.diagonal A)
      nontriv : NonTrivialWithinBudget
                  (Assumptions.oracle A)
                  (Assumptions.cost A)
                  (Assumptions.budget A)
      nontriv = VacuityGuards.someWithin (Assumptions.vacuity A) , witness
    in
    record
      { no-total  = noTotal
      ; witness   = witness
      ; nontrivial = nontriv
      }

  module Q {PS : PB.ProofSystem} = AppKit.MakeDerived (Assumptions PS) (Claim PS) derive
  open Q public using (Pack; assumptionsOf; claimOf; mkPack)
