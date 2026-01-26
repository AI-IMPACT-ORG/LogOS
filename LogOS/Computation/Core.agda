{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Computation.Core where

open import LogOS.Prelude
open import LogOS.Minimal.Con using (ConPreorder; MonoOn)

-- Minimal computation interface: a code carrier with a total step.

record Computation {ℓ : Level} (Code : Set ℓ) : Set (lsuc ℓ) where
  field
    Step  : Code → Code
    Halts : Code → Set ℓ         -- halting predicate (model-chosen)

open Computation public

iterate : ∀ {ℓ Code} → Computation {ℓ} Code → ℕ → Code → Code
iterate C zero    c = c
iterate C (suc n) c = iterate C n (Computation.Step C c)

iterate-+
  : ∀ {ℓ Code}
    (C : Computation {ℓ} Code)
    (m n : ℕ)
    (c : Code)
  → iterate C (m + n) c ≡ iterate C n (iterate C m c)
iterate-+ C zero    n c = refl
iterate-+ C (suc m) n c = iterate-+ C m n (Computation.Step C c)

-- Iteration preserves monotonicity on a constraint preorder.
--
-- This is a small but reusable bridge between operational iteration (`iterate`)
-- and order-theoretic reasoning (preorders on states).

iterate-mono
  : ∀ {ℓ}
    (CP : ConPreorder ℓ)
    (f : ConPreorder.Con CP → ConPreorder.Con CP)
    (mono : MonoOn CP f)
  → ∀ n {x y}
  → ConPreorder._⊑_ CP x y
  → ConPreorder._⊑_ CP (iterate (record { Step = f ; Halts = λ _ → Topℓ }) n x)
                     (iterate (record { Step = f ; Halts = λ _ → Topℓ }) n y)
iterate-mono CP f mono zero    p = p
iterate-mono CP f mono (suc n) p = iterate-mono CP f mono n (mono p)

-- View a total step function as a computation (halting ignored).
stepComputation : ∀ {ℓ} {Code : Set ℓ} → (Code → Code) → Computation Code
stepComputation step = record { Step = step ; Halts = λ _ → Topℓ }

iterateStep : ∀ {ℓ} {Code : Set ℓ} → (Code → Code) → ℕ → Code → Code
iterateStep step n c = iterate (stepComputation step) n c

-- Strict one-step simulation between step functions (for “universality transport”).
--
-- This lives in a nested module so `API.Minimal` can re-export `Computation.Core`
-- without flooding the global namespace with projections like `map`.

module StepSimulation where

  record StepSim {ℓ₁ ℓ₂ : Level}
                 (A : Set ℓ₁) (B : Set ℓ₂)
                 (stepA : A → A) (stepB : B → B)
                 : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
    field
      map       : A → B
      step-comm : ∀ a → map (stepA a) ≡ stepB (map a)

  infixr 40 _∘StepSim_

  _∘StepSim_
    : ∀ {ℓ₁ ℓ₂ ℓ₃}
      {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
      {stepA : A → A} {stepB : B → B} {stepC : C → C}
    → StepSim B C stepB stepC
    → StepSim A B stepA stepB
    → StepSim A C stepA stepC
  _∘StepSim_ g f =
    record
      { map = λ a → StepSim.map g (StepSim.map f a)
      ; step-comm = λ a →
          trans
            (cong (StepSim.map g) (StepSim.step-comm f a))
            (StepSim.step-comm g (StepSim.map f a))
      }

  iterateStep-map
    : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂}
      (stepA : A → A) (stepB : B → B)
      (S : StepSim A B stepA stepB)
    → ∀ n a
    → StepSim.map S (iterateStep stepA n a) ≡ iterateStep stepB n (StepSim.map S a)
  iterateStep-map _ _ _ zero    _ = refl
  iterateStep-map stepA stepB S (suc n) a =
    trans
      (iterateStep-map stepA stepB S n (stepA a))
      (cong (iterateStep stepB n) (StepSim.step-comm S a))
