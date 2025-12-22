{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Universality where

open import LogOS.Prelude

open import LogOS.Computation.Core using (Computation; iterate)

open import LogOS.Domain.UniversalIR.Core
  using
    ( UCode; UM; UL; UE; UQ; UQC
    ; stepU; simulate
    )

open import LogOS.Domain.UniversalIR.Core.Minsky using (MinskyCode; stepM)
open import LogOS.Domain.UniversalIR.Core.Lambda using (LambdaCode; stepLC)
open import LogOS.Domain.UniversalIR.Core.Ethereum using (EVMCode; stepE)
open import LogOS.Domain.UniversalIR.Core.QuantumOracle using (QuantumCode; stepQ)
open import LogOS.Domain.UniversalIR.Core.QuantumCircuit using (QuantumCircuitCode; stepQC)

-- ============================================================================
-- “Universality transport” (tiny, explicit)
--
-- `UCode` is a coproduct of multiple paradigms. Each branch embeds into the
-- shared stepper `stepU` by construction, so any step-based statement about a
-- branch can be transported to `UCode` just by composing with the injection.
-- ============================================================================

-- A minimal step-simulation interface (independent of SchemeCategory/Norm).

-- View a plain step function as a trivial computation (halting ignored).
CompOf : ∀ {ℓ} {A : Set ℓ} → (A → A) → Computation A
CompOf step = record { Step = step ; Halts = λ _ → Topℓ }

record StepSim {ℓ₁ ℓ₂ : Level} (A : Set ℓ₁) (B : Set ℓ₂)
               (stepA : A → A) (stepB : B → B) : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field
    embed    : A → B
    step-comm : ∀ a → embed (stepA a) ≡ stepB (embed a)

open StepSim public

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
    { embed = λ a → embed g (embed f a)
    ; step-comm = λ a →
        trans (cong (embed g) (step-comm f a))
              (step-comm g (embed f a))
    }

iter : ∀ {ℓ} {A : Set ℓ} → (A → A) → ℕ → A → A
iter step n a = iterate (CompOf step) n a

iterSim
  : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂}
    (stepA : A → A) (stepB : B → B)
    (S : StepSim A B stepA stepB)
    → ∀ n a → embed S (iter stepA n a) ≡ iter stepB n (embed S a)
iterSim _ _ S zero    _ = refl
iterSim stepA stepB S (suc n) a =
  trans
    (iterSim stepA stepB S n (stepA a))
    (cong (iter stepB n) (step-comm S a))

-- Branch embeddings into `UCode` commute with one step (definitionally).

step-UM : ∀ m → stepU (UM m) ≡ UM (stepM m)
step-UM _ = refl

step-UL : ∀ l → stepU (UL l) ≡ UL (stepLC l)
step-UL _ = refl

step-UE : ∀ e → stepU (UE e) ≡ UE (stepE e)
step-UE _ = refl

step-UQ : ∀ q → stepU (UQ q) ≡ UQ (stepQ q)
step-UQ _ = refl

step-UQC : ∀ q → stepU (UQC q) ≡ UQC (stepQC q)
step-UQC _ = refl

-- Branch simulations (as StepSim values), suitable for composition.

MinskySim : StepSim MinskyCode UCode stepM stepU
MinskySim = record { embed = UM ; step-comm = λ _ → refl }

LambdaSim : StepSim LambdaCode UCode stepLC stepU
LambdaSim = record { embed = UL ; step-comm = λ _ → refl }

EthereumSim : StepSim EVMCode UCode stepE stepU
EthereumSim = record { embed = UE ; step-comm = λ _ → refl }

QuantumOracleSim : StepSim QuantumCode UCode stepQ stepU
QuantumOracleSim = record { embed = UQ ; step-comm = λ _ → refl }

QuantumCircuitSim : StepSim QuantumCircuitCode UCode stepQC stepU
QuantumCircuitSim = record { embed = UQC ; step-comm = λ _ → refl }

-- Core transport lemma (lightweight universality upgrade):
--
-- Given a step-simulation of a paradigm into Minsky, composing with the Minsky
-- injection yields a step-simulation into the shared `UCode` process.

liftThroughMinsky
  : ∀ {ℓ} {A : Set ℓ} {stepA : A → A}
    → StepSim A MinskyCode stepA stepM
    → StepSim A UCode stepA stepU
liftThroughMinsky sim = MinskySim ∘StepSim sim

-- And therefore, running the universal stepper restricted to a branch is the
-- same as iterating the branch stepper and then re-injecting.

simulateUM : ∀ n m → simulate n (UM m) ≡ UM (iter stepM n m)
simulateUM zero    _ = refl
simulateUM (suc n) m =
  trans
    (simulateUM n (stepM m))
    refl

simulateUL : ∀ n l → simulate n (UL l) ≡ UL (iter stepLC n l)
simulateUL zero    _ = refl
simulateUL (suc n) l =
  trans
    (simulateUL n (stepLC l))
    refl

simulateUE : ∀ n e → simulate n (UE e) ≡ UE (iter stepE n e)
simulateUE zero    _ = refl
simulateUE (suc n) e =
  trans
    (simulateUE n (stepE e))
    refl

simulateUQ : ∀ n q → simulate n (UQ q) ≡ UQ (iter stepQ n q)
simulateUQ zero    _ = refl
simulateUQ (suc n) q =
  trans
    (simulateUQ n (stepQ q))
    refl

simulateUQC
  : ∀ n q → simulate n (UQC q) ≡ UQC (iter stepQC n q)
simulateUQC zero    _ = refl
simulateUQC (suc n) q =
  trans
    (simulateUQC n (stepQC q))
    refl
