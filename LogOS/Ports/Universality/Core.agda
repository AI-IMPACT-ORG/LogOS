{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Universality.Core where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; intro)
open import LogOS.LT.ConPreorder using (ConPreorder; Con; ≈-refl)
open import LogOS.LT.Kernel using (Kernel; Code; decodeView)
open import LogOS.LT.Hom.Core using (KernelHom; mkKernelHomParts)
open import LogOS.LT.View.Roles using (DecodeView)
open import LogOS.Ports.CriticalParameter using (CriticalCut; principalCut)
open import LogOS.Prelude.Nat.Order using (_≤ℕ_; z≤n; s≤s)
import LogOS.Ports.Universality.Fuel as Fuel
open import LogOS.Ports.Universality.NatBoundary using (NatBoundary)

-- Universal refinement boundary for the first universality base layer.
universalBoundary : ConPreorder lzero lzero
universalBoundary = NatBoundary

-- Small universal code language used by adapters during phase 1.
data UniversalCode : Set lzero where
  halted : ℕ → UniversalCode
  active : ℕ → UniversalCode

universalStep : UniversalCode → UniversalCode
universalStep (halted fuel) = halted fuel
universalStep (active zero) = halted zero
universalStep (active (suc fuel)) = active fuel

-- n-step closure for phase-1 universal execution.
runUniversalWithin : ℕ → UniversalCode → UniversalCode
runUniversalWithin = Fuel.FuelProfile.iter Fuel.NatFuel universalStep

-- Observation into the chosen simulator boundary.
universalObservation : UniversalCode → Con universalBoundary
universalObservation (halted fuel) = fuel
universalObservation (active fuel) = fuel

universalFuelAfter : ℕ → UniversalCode → ℕ
universalFuelAfter budget sourceCode = universalObservation (runUniversalWithin budget sourceCode)

universalFuelAfter-active-halt-zero : ∀ budget →
  universalFuelAfter budget (active zero) ≡ universalFuelAfter budget (halted zero)
universalFuelAfter-active-halt-zero zero = refl
universalFuelAfter-active-halt-zero (suc budget) = refl

universalFuelAfter-successor-active-zero :
  ∀ budget →
  universalFuelAfter (suc budget) (active zero) ≡ universalFuelAfter budget (halted zero)
universalFuelAfter-successor-active-zero budget = refl

universalFuelAfter-active-suc :
  ∀ budget fuel →
  universalFuelAfter (suc budget) (active (suc fuel)) ≡
  universalFuelAfter budget (active fuel)
universalFuelAfter-active-suc budget fuel = refl

BudgetEnough : ℕ → ℕ → Set
BudgetEnough fuel budget = fuel ≤ℕ budget

FuelExhausted : ℕ → ℕ → Set
FuelExhausted fuel budget =
  LogOS.LT.ConPreorder._⊑_ universalBoundary
    (universalFuelAfter budget (active fuel))
    zero

criticalBudget
  : (fuel : ℕ)
  → CriticalCut universalBoundary (λ budget → BudgetEnough fuel budget)
criticalBudget fuel = principalCut universalBoundary fuel

universalFuelAfter-halted-zero
  : ∀ budget
  → universalFuelAfter budget (halted zero) ≡ zero
universalFuelAfter-halted-zero zero = refl
universalFuelAfter-halted-zero (suc budget) =
  universalFuelAfter-halted-zero budget

universalFuelAfter-zeroWhenEnough
  : ∀ fuel budget
  → BudgetEnough fuel budget
  → universalFuelAfter budget (active fuel) ≡ zero
universalFuelAfter-zeroWhenEnough zero budget z≤n =
  trans
    (universalFuelAfter-active-halt-zero budget)
    (universalFuelAfter-halted-zero budget)
universalFuelAfter-zeroWhenEnough (suc fuel) zero ()
universalFuelAfter-zeroWhenEnough (suc fuel) (suc budget) (s≤s enough) =
  trans
    (universalFuelAfter-active-suc budget fuel)
    (universalFuelAfter-zeroWhenEnough fuel budget enough)

≤ℕ-zero→≡zero
  : ∀ {n}
  → n ≤ℕ zero
  → n ≡ zero
≤ℕ-zero→≡zero {zero} z≤n = refl

universalFuelAfter-zeroOnlyWhenEnough
  : ∀ fuel budget
  → universalFuelAfter budget (active fuel) ≡ zero
  → BudgetEnough fuel budget
universalFuelAfter-zeroOnlyWhenEnough zero budget _ = z≤n
universalFuelAfter-zeroOnlyWhenEnough (suc fuel) zero ()
universalFuelAfter-zeroOnlyWhenEnough (suc fuel) (suc budget) zeroEq =
  s≤s (universalFuelAfter-zeroOnlyWhenEnough fuel budget zeroEq)

fuelExhausted→budgetEnough
  : ∀ fuel budget
  → FuelExhausted fuel budget
  → BudgetEnough fuel budget
fuelExhausted→budgetEnough fuel budget exhausted =
  universalFuelAfter-zeroOnlyWhenEnough fuel budget (≤ℕ-zero→≡zero exhausted)

fuelExhausted↔budgetEnough
  : ∀ fuel budget
  → FuelExhausted fuel budget ↔ BudgetEnough fuel budget
fuelExhausted↔budgetEnough fuel budget =
  intro
    (fuelExhausted→budgetEnough fuel budget)
    (budgetEnough→fuelExhausted fuel budget)
  where
    budgetEnough→fuelExhausted
      : ∀ fuel' budget'
      → BudgetEnough fuel' budget'
      → FuelExhausted fuel' budget'
    budgetEnough→fuelExhausted fuel' budget' enough
      rewrite universalFuelAfter-zeroWhenEnough fuel' budget' enough = z≤n

-- The universal center kernel entrypoint.
universalKernel : Kernel lzero lzero lzero
universalKernel =
  record
    { bnd = universalBoundary
    ; Code = UniversalCode
    ; decode = universalObservation
    }

runUniversalWithin-observation : ∀ nCode →
  ∀ sourceCode → universalObservation (runUniversalWithin nCode sourceCode) ≡
    universalFuelAfter nCode sourceCode
runUniversalWithin-observation nCode sourceCode = refl

universalObservationView : DecodeView UniversalCode universalBoundary
universalObservationView = decodeView universalKernel

fuelKernel
  : ∀ {ℓCode : Level}
    {CodeType : Set ℓCode}
  → (CodeType → ℕ)
  → Kernel lzero lzero ℓCode
fuelKernel {CodeType = CodeType} fuel =
  record
    { bnd = universalBoundary
    ; Code = CodeType
    ; decode = fuel
    }

fuelKernelToUniversal
  : ∀ {ℓCode : Level}
    {CodeType : Set ℓCode}
  → (fuel : CodeType → ℕ)
  → KernelHom (fuelKernel fuel) universalKernel
fuelKernelToUniversal fuel =
  mkKernelHomParts
    (record
      { map∂ = λ observationValue → observationValue
      ; map∂-mono = λ h → h
      })
    (record
      { mapCode = λ sourceCode → active (fuel sourceCode)
      ; decode-mapCode = λ sourceCode → ≈-refl universalBoundary (fuel sourceCode)
      })

record FuelAdapter
  {ℓCode : Level}
  (CodeType : Set ℓCode)
  : Set (lsuc ℓCode) where
  field
    fuel : CodeType → ℕ

  kernel : Kernel lzero lzero ℓCode
  kernel = fuelKernel fuel

  toUniversal : KernelHom kernel universalKernel
  toUniversal = fuelKernelToUniversal fuel

mkFuelAdapter
  : ∀ {ℓCode : Level}
    {CodeType : Set ℓCode}
  → (CodeType → ℕ)
  → FuelAdapter CodeType
mkFuelAdapter fuel = record { fuel = fuel }

fuelBoundary
  : ∀ {ℓCode : Level}
    {CodeType : Set ℓCode}
  → FuelAdapter CodeType
  → CodeType
  → ℕ
fuelBoundary = FuelAdapter.fuel

mkFuelKernel
  : ∀ {ℓCode : Level}
    {CodeType : Set ℓCode}
  → FuelAdapter CodeType
  → Kernel lzero lzero ℓCode
mkFuelKernel = FuelAdapter.kernel

mkFuelToUniversal
  : ∀ {ℓCode : Level}
    {CodeType : Set ℓCode}
  → (A : FuelAdapter CodeType)
  → KernelHom (mkFuelKernel A) universalKernel
mkFuelToUniversal = FuelAdapter.toUniversal

fuelKernelHom
  : ∀ {ℓCode : Level}
    {CodeType : Set ℓCode}
  → (A : FuelAdapter CodeType)
  → KernelHom (mkFuelKernel A) universalKernel
fuelKernelHom = mkFuelToUniversal
