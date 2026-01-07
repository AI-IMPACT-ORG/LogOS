{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.Examples.GoldenPathMinsky where

open import LogOS.Prelude

open import Data.NatOrder using (_≤ℕ_; ≤ℕ-refl; z≤n; s≤s; weakenRight; trans≤ℕ)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.ScaleOps using (ScaleOps)
open import LogOS.Kernel.Graded

open import LogOS.Domain.Complexity.Poly using (PolyPred)
import LogOS.Domain.Complexity.PolyGrade as PG
import LogOS.Domain.Complexity.Examples.GoldenPath as GP
import LogOS.Domain.Complexity.UniversalIRCM as UIR

import LogOS.Computation.Scheme as Sch

open import LogOS.Domain.UniversalIR.Core
  using (UCode; MinskyCode; HALT; INC; DECJZ; lookupDefault; prog; pc; stepM)
import LogOS.Domain.UniversalIR.Schemes as Schemes
import LogOS.Domain.UniversalIR.Examples.SchemeChoices as Choices
import LogOS.Domain.UniversalIR.KernelRichG as KR

-- Concrete scheme factorization (machines as schemes):
-- Minsky schemes factor through the universal UProcess.
module SchemeFactorization where
  open Schemes public using (minskyMachineScheme)
  open Choices public using (minskyFactorsThroughU; minskyCostFactorsThroughU)

-- Minsky-backed instantiation shell for the GoldenPath pipeline.
-- This fixes the computation model to the Minsky scheme; the kernel embedding
-- remains abstract.

module For
  {Sig : LogOSSignature lzero}
  {Q : QAdapter lzero}
  (K : GradedKernel Sig Q)
  (Ops : ScaleOps Q)
  (toCodeK : UCode → GradedKernel.Code K)
  (fromCodeK : GradedKernel.Code K → UCode)
  (gradeBound : ℕ → QAdapter.Scale Q)
  (Pℕ : PolyPred)
  where

  M : UIR.StandardCMᴵᴿ {ℓ = lzero}
  M = UIR.mkIRCM Pℕ UIR.minsky

  open UIR.StandardCMᴵᴿ M renaming
    ( Input  to Inputᵀ
    ; size   to sizeᵀ
    ; wsize  to wsizeᵀ
    )

  module TR = UIR.TR K toCodeK fromCodeK gradeBound M

  module PGN = PG.FromNat Q Pℕ gradeBound

  module Core =
    GP.Core K Inputᵀ sizeᵀ
      TR.DetRun TR.VerRun TR.VerRunWith
      PGN.polyPredG

  open Core public

  -- Witness size induced by the Minsky scheme's UCode witness sizing.
  WSize : GradedKernel.Code K → ℕ
  WSize w = wsizeᵀ (fromCodeK w)

  -- Operational scale: interpret grades as step budgets.
  open ScaleOps Ops renaming (budget to budgetG; steps to stepsG)

  Budget : QAdapter.Scale Q → ℕ
  Budget g = stepsG (budgetG g)

  SizeBudget : Set
  SizeBudget = ∀ x → sizeᵀ x ≤ℕ Budget (gradeBound (sizeᵀ x))

  FuelBudget : Set
  FuelBudget = ∀ x → UIR.fuel UIR.minsky x ≤ℕ Budget (gradeBound (sizeᵀ x))

  costSteps : (ℕ × ℕ) → ℕ
  costSteps (n , _) = n

  stepCostM≤1 : ∀ m → costSteps (Schemes.stepCostM m) ≤ℕ suc zero
  stepCostM≤1 m with lookupDefault HALT (prog m) (pc m)
  ... | HALT = z≤n
  ... | INC _ _ = ≤ℕ-refl
  ... | DECJZ _ _ _ = ≤ℕ-refl

  ≤1+≤n→≤suc : ∀ {a b n} → a ≤ℕ suc zero → b ≤ℕ n → a + b ≤ℕ suc n
  ≤1+≤n→≤suc z≤n      b≤n = weakenRight b≤n
  ≤1+≤n→≤suc (s≤s z≤n) b≤n = s≤s b≤n

  costExec≤steps : ∀ n (m : MinskyCode) →
    costSteps (Sch.costExec Schemes.minskyMachineScheme n m) ≤ℕ n
  costExec≤steps zero    _ = z≤n
  costExec≤steps (suc n) m =
    ≤1+≤n→≤suc (stepCostM≤1 m) (costExec≤steps n (stepM m))

  cost≤fuel : ∀ x →
    costSteps (Sch.cost Schemes.minskyMachineScheme x) ≤ℕ UIR.fuel UIR.minsky x
  cost≤fuel x =
    costExec≤steps
      (UIR.fuel UIR.minsky x)
      (Sch.compile Schemes.minskyMachineScheme x)

  cost≤budget : FuelBudget → ∀ x →
    costSteps (Sch.cost Schemes.minskyMachineScheme x) ≤ℕ
    Budget (gradeBound (sizeᵀ x))
  cost≤budget fuel≤budget x =
    trans≤ℕ (cost≤fuel x) (fuel≤budget x)

  module Align =
    GP.ClassicalAlignment
      K Inputᵀ sizeᵀ
      TR.DetRun TR.VerRun TR.VerRunWith
      gradeBound WSize Pℕ

  open Align public

-- Fully concrete instantiation: kernel code is UCode and decode is id,
-- with a time-indexed graded Flow (simulate (budget g)).
module Concrete (Pℕ : PolyPred) where
  open KR
  open QAdapter Q using (τ)

  gradeBound : ℕ → QAdapter.Scale Q
  gradeBound n = τ n

  module Inst =
    For {Sig = KR.Sig} {Q = KR.Q}
      KR.GUKR
      KR.Ops
      (λ u → u)
      (λ u → u)
      gradeBound
      Pℕ

  open Inst public

  size≤budget : Inst.SizeBudget
  size≤budget _ = ≤ℕ-refl
