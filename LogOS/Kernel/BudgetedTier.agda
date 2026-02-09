{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.BudgetedTier where

-- Optional strengthening of the `GTier` interface:
-- provide an ordered monoid structure on steps/budgets so `BoxAt` supports
-- monotonicity-in-budget and lax composition.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (ConPreorder; BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel
open import LogOS.Kernel.Shape as Core hiding (FlowCode)

import LogOS.Kernel as K
import LogOS.Kernel.UngradedKernel as UK
import LogOS.Kernel.Graded as KG
import LogOS.Kernel.FromUngradedKernel as LKFromUngraded
import LogOS.Kernel.FromGradedKernel as LKFromGraded

record BudgetedTier
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  : Set (lsuc ℓ) where
  private
    CP∂ : ConPreorder ℓ
    CP∂ = BulkBoundary.bnd (Kernel.BB K)

  open ConPreorder CP∂ using (Con; _⊑_)
  open GTier (Kernel.G K) renaming (Step to Grade)

  infix 4 _≤g_
  infixl 7 _·g_

  field
    _≤g_     : Grade → Grade → Set ℓ
    ≤g-refl  : ∀ {g} → _≤g_ g g
    ≤g-trans : ∀ {a b c} → _≤g_ a b → _≤g_ b c → _≤g_ a c

    _·g_     : Grade → Grade → Grade
    ε        : Grade
    ·g-assoc : ∀ a b c → (_·g_ (_·g_ a b) c) ≡ (_·g_ a (_·g_ b c))
    ·g-idl   : ∀ a → (_·g_ ε a) ≡ a
    ·g-idr   : ∀ a → (_·g_ a ε) ≡ a

    -- Saturation is “top” w.r.t. the step preorder.
    sat-top  : ∀ g → _≤g_ g (GTier.sat (Kernel.G K))

    -- Flow is monotone in the step index.
    mono-grade
      : ∀ {g g'}
      → _≤g_ g g'
      → ∀ c
      → _⊑_ (GTier.Flow (Kernel.G K) g c) (GTier.Flow (Kernel.G K) g' c)

    -- Lax step composition matches monoid multiplication.
    comp-lax
      : ∀ g g' c
      → _⊑_
          (GTier.Flow (Kernel.G K) g'
            (GTier.Flow (Kernel.G K) g c))
          (GTier.Flow (Kernel.G K) (_·g_ g g') c)

open BudgetedTier public

-- Any budgeted tier induces the existing “step ≤ sat” assumption.

stepOrderOfBudgetedTier
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
  → BudgetedTier K
  → StepOrder K
stepOrderOfBudgetedTier {K = K} BT c =
  mono-grade BT (sat-top BT (GTier.step (Kernel.G K))) c

module Derived
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  (BT : BudgetedTier K)
  where

  open BudgetedTier BT
    renaming
      ( _≤g_      to _≤b_
      ; _·g_      to _·b_
      ; sat-top   to sat-topᵇ
      ; mono-grade to mono-gradeᵇ
      ; comp-lax  to comp-laxᵇ
      )

  boxAt-mono-grade
    : ∀ {g g'}
    → _≤b_ g g'
    → (γ : Kernel.Code K)
    → Core.Code≤ (Kernel.shape K) (BoxAt K g γ) (BoxAt K g' γ)
  boxAt-mono-grade {g} {g'} g≤g' γ
    rewrite decode-BoxAt K g γ | decode-BoxAt K g' γ
    = mono-gradeᵇ g≤g' (Kernel.decode K γ)

  boxAt-comp-lax
    : ∀ g g' (γ : Kernel.Code K)
    → Core.Code≤ (Kernel.shape K)
        (BoxAt K g' (BoxAt K g γ))
        (BoxAt K (_·b_ g g') γ)
  boxAt-comp-lax g g' γ
    rewrite decode-BoxAt K g' (BoxAt K g γ)
          | decode-BoxAt K g γ
          | decode-BoxAt K (_·b_ g g') γ
    = comp-laxᵇ g g' (Kernel.decode K γ)

  boxAt≤Box
    : ∀ g (γ : Kernel.Code K)
    → Core.Code≤ (Kernel.shape K) (BoxAt K g γ) (Box K γ)
  boxAt≤Box g γ =
    boxAt-mono-grade (sat-topᵇ g) γ

-- --------------------------------------------------------------------------
-- Canonical instances for logic-kernel bridges
-- --------------------------------------------------------------------------

budgetedTierFromUngradedKernel
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K₀ : UK.UngradedKernel Sig Q)
  → BudgetedTier (LKFromUngraded.asKernel K₀)
budgetedTierFromUngradedKernel K₀ =
  let
    K'  = LKFromUngraded.asKernel K₀
    CP∂ = BulkBoundary.bnd (Kernel.BB K')
  in
  record
    { _≤g_ = λ _ _ → ⊤
    ; ≤g-refl = tt
    ; ≤g-trans = λ _ _ → tt
    ; _·g_ = λ _ _ → tt
    ; ε = tt
    ; ·g-assoc = λ _ _ _ → refl
    ; ·g-idl = λ { ttℓ → refl }
    ; ·g-idr = λ { ttℓ → refl }
    ; sat-top = λ _ → tt
    ; mono-grade = λ _ _ → ConPreorder.refl CP∂
    ; comp-lax = λ _ _ c → GTier.idemp-sat (Kernel.G K') c
    }

budgetedTierFromGradedKernel
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K₀ : KG.GradedKernel Sig Q)
  → BudgetedTier (LKFromGraded.asKernel K₀)
budgetedTierFromGradedKernel {Q = Q} K₀ =
  record
    { _≤g_ = QAdapter._≤s_ Q
    ; ≤g-refl = QAdapter.≤s-refl Q
    ; ≤g-trans = QAdapter.≤s-trans Q
    ; _·g_ = QAdapter._·_ Q
    ; ε = QAdapter.e Q
    ; ·g-assoc = QAdapter.·-assoc Q
    ; ·g-idl = QAdapter.·-idl Q
    ; ·g-idr = QAdapter.·-idr Q
    ; sat-top = Truth.GuardedCore.GradedClosure.sat-top (KG.GradedKernel.GTruth K₀)
    ; mono-grade = Truth.GuardedCore.GradedClosure.mono-grade (KG.GradedKernel.GTruth K₀)
    ; comp-lax = Truth.GuardedCore.GradedClosure.comp-lax (KG.GradedKernel.GTruth K₀)
    }
