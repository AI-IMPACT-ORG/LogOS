{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Universality where

open import LogOS.Prelude

open import LogOS.Computation.Core using (iterateStep)
import LogOS.Computation.Core as CompCore
module Sim = CompCore.StepSimulation
open Sim using (StepSim; _∘StepSim_)
open Sim.StepSim public renaming (map to embed)

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

iterSim
  : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂}
    (stepA : A → A) (stepB : B → B)
    (S : StepSim A B stepA stepB)
    → ∀ n a → embed S (iterateStep stepA n a) ≡ iterateStep stepB n (embed S a)
iterSim stepA stepB S n a = Sim.iterateStep-map stepA stepB S n a

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
MinskySim = record { map = UM ; step-comm = λ _ → refl }

LambdaSim : StepSim LambdaCode UCode stepLC stepU
LambdaSim = record { map = UL ; step-comm = λ _ → refl }

EthereumSim : StepSim EVMCode UCode stepE stepU
EthereumSim = record { map = UE ; step-comm = λ _ → refl }

QuantumOracleSim : StepSim QuantumCode UCode stepQ stepU
QuantumOracleSim = record { map = UQ ; step-comm = λ _ → refl }

QuantumCircuitSim : StepSim QuantumCircuitCode UCode stepQC stepU
QuantumCircuitSim = record { map = UQC ; step-comm = λ _ → refl }

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

simulateUM : ∀ n m → simulate n (UM m) ≡ UM (iterateStep stepM n m)
simulateUM zero    _ = refl
simulateUM (suc n) m =
  trans
    (simulateUM n (stepM m))
    refl

simulateUL : ∀ n l → simulate n (UL l) ≡ UL (iterateStep stepLC n l)
simulateUL zero    _ = refl
simulateUL (suc n) l =
  trans
    (simulateUL n (stepLC l))
    refl

simulateUE : ∀ n e → simulate n (UE e) ≡ UE (iterateStep stepE n e)
simulateUE zero    _ = refl
simulateUE (suc n) e =
  trans
    (simulateUE n (stepE e))
    refl

simulateUQ : ∀ n q → simulate n (UQ q) ≡ UQ (iterateStep stepQ n q)
simulateUQ zero    _ = refl
simulateUQ (suc n) q =
  trans
    (simulateUQ n (stepQ q))
    refl

simulateUQC
  : ∀ n q → simulate n (UQC q) ≡ UQC (iterateStep stepQC n q)
simulateUQC zero    _ = refl
simulateUQC (suc n) q =
  trans
    (simulateUQC n (stepQC q))
    refl
