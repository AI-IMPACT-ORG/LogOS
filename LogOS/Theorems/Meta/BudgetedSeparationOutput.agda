{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.BudgetedSeparationOutput where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_; ⊥; ⊥-elim; _↔_; to)

open import LogOS.Prelude.Nat using (ℕ)
open import LogOS.Prelude.NatOrder using (_≤ℕ_; dec≤ℕ)
open import LogOS.Prelude.Product using (Σ; _,_; proj₁; proj₂)
open import LogOS.Prelude.Sum using (_⊎_; inj₁; inj₂)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Kernel
import LogOS.Theorems.Meta.SpectralSeparationOutput as SSO
open import LogOS.Theorems.Meta.Assumptions.Diagonal using
  (TruthDiagonal; TruthDiagonalC; liar-witnessC; no-totalC; liar-witness; no-total)

-- Quantitative upgrade of `SpectralSeparationOutput`:
-- equip witnesses with a cost/size, and define a derived observer that only
-- accepts witnesses within a fixed budget `b`.
--
-- Interpretation: “observable within budget b” is not a blanket predicate; it is
-- an operational/quantitative interface that can be instantiated by:
-- - proof length / certificate size (Cook–Reckhow),
-- - time-bounded Kolmogorov complexity (Kt),
-- - physical non-unitary event budgets, etc.

record WitnessCost {ℓ} (Witness : Set ℓ) : Set (lsuc ℓ) where
  field
    cost : Witness → ℕ


module For
  {ℓ}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  {K   : Kernel Sig Q}
  (O   : SSO.SpectralSeparationOutput K)
  (C   : WitnessCost (SSO.SpectralSeparationOutput.Witness O))
  where

  open Kernel K
  open SSO.SpectralSeparationOutput O
  open WitnessCost C

  Witness≤ : ℕ → Set ℓ
  Witness≤ b = Σ Witness (λ w → cost w ≤ℕ b)

  filter≤ : (b : ℕ) → (Witness ⊎ ⊤ {ℓ = lzero}) → (Witness≤ b ⊎ ⊤ {ℓ = lzero})
  filter≤ b (inj₂ ttℓ) = inj₂ ttℓ
  filter≤ b (inj₁ w) with dec≤ℕ (cost w) b
  ... | inj₁ le = inj₁ (w , le)
  ... | inj₂ _  = inj₂ ttℓ

  -- Budget-filtered inference: if `infer` produces a witness whose cost exceeds
  -- the budget, we treat it as “not observable within budget”.
  infer≤ : (b : ℕ) → Code → Witness≤ b ⊎ ⊤ {ℓ = lzero}
  infer≤ b γ = filter≤ b (infer γ)

  -- Derived partial-output surface for a fixed budget.
  Budgeted : (b : ℕ) → SSO.SpectralSeparationOutput K
  Budgeted b = record
    { core = record
        { Witness = Witness≤ b
        ; infer   = infer≤ b
        ; ext     = ext≤ b
        }
    }
    where
      ext≤
        : ∀ b γ₁ γ₂
          → _≈CP_ (BulkBoundary.bnd BB) (decode γ₁) (decode γ₂)
          → infer≤ b γ₁ ≡ infer≤ b γ₂
      ext≤ b γ₁ γ₂ dec≈ = cong (filter≤ b) (ext γ₁ γ₂ dec≈)

  -- Derived partial-output surface for a budget function B : Code → ℕ.
  --
  -- Note: to preserve extensionality, the budget function must itself be
  -- decode-extensional up to decoded mutual refinement (e.g. depend only on
  -- `decode γ` or its `size`).

  filterBudget : ℕ → (Witness ⊎ ⊤ {ℓ = lzero}) → (Witness ⊎ ⊤ {ℓ = lzero})
  filterBudget b (inj₂ ttℓ) = inj₂ ttℓ
  filterBudget b (inj₁ w) with dec≤ℕ (cost w) b
  ... | inj₁ _ = inj₁ w
  ... | inj₂ _ = inj₂ ttℓ

  infer≤ᵇ : (B : Code → ℕ) → Code → Witness ⊎ ⊤ {ℓ = lzero}
  infer≤ᵇ B γ = filterBudget (B γ) (infer γ)

  BudgetedBy : (B : Code → ℕ)
              → (Bext
                  : ∀ γ₁ γ₂
                    → _≈CP_ (BulkBoundary.bnd BB) (decode γ₁) (decode γ₂)
                    → B γ₁ ≡ B γ₂)
              → SSO.SpectralSeparationOutput K
  BudgetedBy B Bext = record
    { core = record
        { Witness = Witness
        ; infer   = infer≤ᵇ B
        ; ext     = extᵇ
        }
    }
    where
      extᵇ
        : ∀ γ₁ γ₂
          → _≈CP_ (BulkBoundary.bnd BB) (decode γ₁) (decode γ₂)
          → infer≤ᵇ B γ₁ ≡ infer≤ᵇ B γ₂
      extᵇ γ₁ γ₂ dec≈ =
        cong₂ filterBudget (Bext γ₁ γ₂ dec≈) (ext γ₁ γ₂ dec≈)

  -- A stronger “total observability” claim: the original oracle always returns a
  -- witness within budget `b`.
  UniformBudget : ℕ → Set ℓ
  UniformBudget b =
    ∀ γ → Σ Witness (λ w → infer γ ≡ inj₁ w × cost w ≤ℕ b)

  -- If an oracle is uniformly budget-bounded, then the budgeted observer is total.
  uniformBudget→budgetedTotal
    : ∀ b → UniformBudget b
      → (∀ γ → SSO.SpectralSeparationOutput.HasSeparation (Budgeted b) γ)
  uniformBudget→budgetedTotal b ub γ with ub γ
  ... | (w , (eq , le)) with infer γ | eq
  ... | inj₁ w | refl with dec≤ℕ (cost w) b
  ... | inj₁ le′ = (w , le′) , refl
  ... | inj₂ notLe = ⊥-elim (notLe le)

  -- Quantitative impossibility: for each fixed budget b, diagonalization forces
  -- an explicit input where the budgeted observer must return “undefined”.
  --
  -- This upgrades “no total oracle” to: “no oracle can be total under a fixed budget”.
  budgeted-diagonal-witness
    : ∀ b
      → TruthDiagonal K (SSO.SpectralSeparationOutput.HasSeparation (Budgeted b))
      → Σ Code (λ γ → SSO.SpectralSeparationOutput.NoSeparation (Budgeted b) γ)
  budgeted-diagonal-witness b TD =
    SSO.separation-output-diagonal-witness (Budgeted b) TD

  no-uniform-budget
    : ∀ b
      → TruthDiagonal K (SSO.SpectralSeparationOutput.HasSeparation (Budgeted b))
      → ¬ UniformBudget b
  no-uniform-budget b TD ub =
    SSO.separation-output-not-total (Budgeted b) TD (uniformBudget→budgetedTotal b ub)

  -- Budget-function form (ties directly to complexity-style “poly by size” bounds):
  --
  -- For any budget function `B`, diagonalization blocks a total observer that is
  -- forced to stay within `B γ` on each input γ.
  no-total-within
    : ∀ (B : Code → ℕ)
      → (Bext
          : ∀ γ₁ γ₂
            → _≈CP_ (BulkBoundary.bnd BB) (decode γ₁) (decode γ₂)
            → B γ₁ ≡ B γ₂)
      → TruthDiagonal K (SSO.SpectralSeparationOutput.HasSeparation (BudgetedBy B Bext))
      → ¬ (∀ γ → SSO.SpectralSeparationOutput.HasSeparation (BudgetedBy B Bext) γ)
  no-total-within B Bext TD =
    SSO.separation-output-not-total (BudgetedBy B Bext) TD

  -- ==========================================================================
  -- Generalized budget interface (graded-kernel friendly)
  --
  -- The definitions above “compile” budgets down to ℕ so we can *compute* a
  -- filtered observer (`infer≤`) using `dec≤ℕ`.
  --
  -- For many LogOS uses (especially with `GradedKernel`), budgets naturally live
  -- in a quantale scale (e.g. `QAdapter.Scale Q`, such as `QNat2`), whose order is
  -- not necessarily decidable. In that setting, we still get a clean
  -- *anti-totality* theorem: no extensional oracle can be total while also
  -- satisfying an abstract “within budget” predicate.
  --
  -- This variant does not build a filtered `infer≤`; instead it states
  -- “totality-within-budget” directly as a predicate and diagonalizes against it.
  -- ==========================================================================

-- Convenience re-exports: expose the main budgeted lemmas at the top-level
-- (parameterised by `O` and `C`) so downstream modules and literate docs can
-- import them without manually opening `For`.
module _
  {ℓ}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  {K   : Kernel Sig Q}
  (O   : SSO.SpectralSeparationOutput K)
  (C   : WitnessCost (SSO.SpectralSeparationOutput.Witness O))
  where
  open For O C public using
    ( Witness≤
    ; Budgeted
    ; BudgetedBy
    ; UniformBudget
    ; uniformBudget→budgetedTotal
    ; budgeted-diagonal-witness
    ; no-uniform-budget
    ; no-total-within
    )
