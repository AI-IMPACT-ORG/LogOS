{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Adapters.Universality.PreQuantumCircuit where

-- Universality adapter: minimal prequantum-circuit-fuel kernel into the universal fuel kernel.

open import LogOS.Prelude
open import LogOS.LT.Kernel using (Kernel; Code)
open import LogOS.LT.Hom using (KernelHom)
import LogOS.Ports.Universality.Fuel as Fuel

import LogOS.Ports.Universality.Core as Core
import LogOS.Ports.Universality.Definitional as Def
import LogOS.Ports.Universality.Task as Task

data PreQuantumCircuitCode : Set lzero where
  mkPreQuantumCircuitCode : ℕ → PreQuantumCircuitCode

preQuantumCircuitFuel : PreQuantumCircuitCode → ℕ
preQuantumCircuitFuel (mkPreQuantumCircuitCode fuelValue) = fuelValue

preQuantumCircuitFromPATask : Task.PATask → PreQuantumCircuitCode
preQuantumCircuitFromPATask sourceTask = mkPreQuantumCircuitCode (Task.taskFuel sourceTask)

preQuantumCircuitFromPATask-fuel : ∀ sourceTask →
  preQuantumCircuitFuel (preQuantumCircuitFromPATask sourceTask) ≡ Task.taskFuel sourceTask
preQuantumCircuitFromPATask-fuel sourceTask = refl

preQuantumCircuitFromPAExprTask : Task.PAExprTask → PreQuantumCircuitCode
preQuantumCircuitFromPAExprTask sourceTask = mkPreQuantumCircuitCode (Task.evaluateExpressionTask sourceTask)

preQuantumCircuitFromPAExprTask-fuel : ∀ sourceTask →
  preQuantumCircuitFuel (preQuantumCircuitFromPAExprTask sourceTask) ≡ Task.evaluateExpressionTask sourceTask
preQuantumCircuitFromPAExprTask-fuel sourceTask = refl

preQuantumCircuitStep : PreQuantumCircuitCode → PreQuantumCircuitCode
preQuantumCircuitStep (mkPreQuantumCircuitCode zero) = mkPreQuantumCircuitCode zero
preQuantumCircuitStep (mkPreQuantumCircuitCode (suc fuelValue)) = mkPreQuantumCircuitCode fuelValue

preQuantumCircuitFuelAdapter : Core.FuelAdapter PreQuantumCircuitCode
preQuantumCircuitFuelAdapter =
  Core.mkFuelAdapter preQuantumCircuitFuel

preQuantumCircuitKernel : Kernel lzero lzero lzero
preQuantumCircuitKernel = Core.mkFuelKernel preQuantumCircuitFuelAdapter

runPreQuantumCircuitWithin : ℕ → PreQuantumCircuitCode → PreQuantumCircuitCode
runPreQuantumCircuitWithin = Fuel.FuelProfile.iter Fuel.NatFuel preQuantumCircuitStep

runPreQuantumCircuitWithin-observation : Def.FuelObservationLaw preQuantumCircuitFuel runPreQuantumCircuitWithin
runPreQuantumCircuitWithin-observation zero sourceCode = refl
runPreQuantumCircuitWithin-observation (suc budget) (mkPreQuantumCircuitCode zero) =
  trans
    (runPreQuantumCircuitWithin-observation budget (mkPreQuantumCircuitCode zero))
    (trans
      (Core.universalFuelAfter-active-halt-zero budget)
      (sym (Core.universalFuelAfter-successor-active-zero budget)))
runPreQuantumCircuitWithin-observation (suc budget) (mkPreQuantumCircuitCode (suc fuelValue)) =
  trans
    (runPreQuantumCircuitWithin-observation budget (mkPreQuantumCircuitCode fuelValue))
    (sym (Core.universalFuelAfter-active-suc budget fuelValue))

preQuantumCircuitToUniversal : KernelHom preQuantumCircuitKernel Core.universalKernel
preQuantumCircuitToUniversal = Core.mkFuelToUniversal preQuantumCircuitFuelAdapter
