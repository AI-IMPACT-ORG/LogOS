{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.FlowCurvature where

open import LogOS.Prelude

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.NatOrder using (_≤ℕ_; z≤n; s≤s; ≤ℕ-refl; trans≤ℕ; weakenRight)
open import Data.Product using (Σ; _,_; proj₁; proj₂)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel
open import LogOS.Computation.Core using (Computation; iterate)

-- RG-flavoured quantitative semantics for Flow:
--
-- A budget function B : Code → ℕ measures “how much resource is needed to observe/certify”
-- at a given code. Applying `FlowCode` is the canonical LogOS “regularization step”.
--
-- The *flow curvature* is the drift of the budget under a flow step:
--   ΔB(γ) ≈ B(FlowCode γ) − B γ.
--
-- This module stays fully generic: it does not commit to what the budget means.
-- Concrete instantiations can take B to be:
-- - proof length / certificate size,
-- - time-bounded Kolmogorov (Kt) witnesses,
-- - physical non-unitary capacity budgets,
-- - polynomial bounds p(size(decode γ)), etc.

module For
  {ℓ}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K   : Kernel Sig Q)
  where

  open Kernel K

  FlowComp : Computation Code
  FlowComp = record { Step = FlowCode K ; Halts = λ _ → ⊤ {ℓ = ℓ} }

  iterFlow : ℕ → Code → Code
  iterFlow = iterate FlowComp

  -- A budget function that is decode-extensional (depends only on the boundary constraint).
  record Budget : Set (lsuc ℓ) where
    field
      B    : Code → ℕ
      Bext : ∀ γ₁ γ₂ → decode γ₁ ≡ decode γ₂ → B γ₁ ≡ B γ₂

  -- A bounded-curvature assumption: one flow step increases the budget by at most κ.
  -- (κ = 0 is the “RG fixed-point” / flow-invariant budget discipline.)
  record CurvatureBound (Bud : Budget) : Set (lsuc ℓ) where
    open Budget Bud
    field
      κ   : ℕ
      step≤ : ∀ γ → B (FlowCode K γ) ≤ℕ (B γ + κ)

  -- Iteration lemma: bounded curvature implies linear drift along n flow steps.
  --
  -- This is the precise form of “distance to metalogical limits accumulates under flow”.
  private
    leAddLeft : ∀ b c → c ≤ℕ (b + c)
    leAddLeft zero    c = ≤ℕ-refl
    leAddLeft (suc b) c = weakenRight (leAddLeft b c)

    monoPlusRight : ∀ {a b c} → a ≤ℕ b → (a + c) ≤ℕ (b + c)
    monoPlusRight {b = b} {c = c} z≤n = leAddLeft b c
    monoPlusRight (s≤s p) = s≤s (monoPlusRight p)

    -- Transport ≤ along definitional equality on the right-hand side.
    substRight : ∀ {a b c} → b ≡ c → a ≤ℕ b → a ≤ℕ c
    substRight refl p = p

    +-assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
    +-assoc zero b c = refl
    +-assoc (suc a) b c = cong suc (+-assoc a b c)

    +-identityʳ : ∀ n → n + zero ≡ n
    +-identityʳ zero = refl
    +-identityʳ (suc n) = cong suc (+-identityʳ n)

  iter≤
    : ∀ {Bud : Budget}
      → (CB : CurvatureBound Bud)
      → ∀ n γ
      → Budget.B Bud (iterFlow n γ)
        ≤ℕ (Budget.B Bud γ + (n * CurvatureBound.κ CB))
  iter≤ {Bud = Bud} CB zero γ =
    let bγ = Budget.B Bud γ
        κ  = CurvatureBound.κ CB
        *-zeroˡ : ∀ n → zero * n ≡ zero
        *-zeroˡ _ = refl
        rhs0 : bγ ≡ (bγ + (zero * κ))
        rhs0 = sym (trans (cong (λ t → bγ + t) (*-zeroˡ κ)) (+-identityʳ bγ))
    in
    substRight rhs0 ≤ℕ-refl
  iter≤ {Bud = Bud} CB (suc n) γ =
    let open Budget Bud
        open CurvatureBound CB

        ih : B (iterFlow n (FlowCode K γ)) ≤ℕ (B (FlowCode K γ) + (n * κ))
        ih = iter≤ CB n (FlowCode K γ)

        step : B (FlowCode K γ) ≤ℕ (B γ + κ)
        step = step≤ γ

        drift : (B (FlowCode K γ) + (n * κ)) ≤ℕ ((B γ + κ) + (n * κ))
        drift = monoPlusRight step

        rhsAssoc : ((B γ + κ) + (n * κ)) ≡ (B γ + ((suc n) * κ))
        rhsAssoc =
          trans (+-assoc (B γ) κ (n * κ)) refl
    in
    substRight rhsAssoc (trans≤ℕ ih drift)
