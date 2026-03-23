{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Adapters.Universality.PreQuantum where

-- Universality adapter: minimal prequantum-fuel kernel into the universal fuel kernel.

open import LogOS.Prelude
open import LogOS.Host.Nat using (ℕ; zero; suc)
open import LogOS.LT.Kernel using (Kernel; Code)
open import LogOS.LT.Hom using (KernelHom)
import LogOS.Ports.Universality.Fuel as Fuel

import LogOS.Ports.Universality.Core as Core
import LogOS.Ports.Universality.Definitional as Def
import LogOS.Ports.Universality.Task as Task

data PreQuantumCode : Set lzero where
  mkPreQuantumCode : ℕ → PreQuantumCode

preQuantumFuel : PreQuantumCode → ℕ
preQuantumFuel (mkPreQuantumCode fuelValue) = fuelValue

preQuantumFromPATask : Task.PATask → PreQuantumCode
preQuantumFromPATask sourceTask = mkPreQuantumCode (Task.taskFuel sourceTask)

preQuantumFromPATask-fuel : ∀ sourceTask →
  preQuantumFuel (preQuantumFromPATask sourceTask) ≡ Task.taskFuel sourceTask
preQuantumFromPATask-fuel sourceTask = refl

preQuantumFromPAExprTask : Task.PAExprTask → PreQuantumCode
preQuantumFromPAExprTask sourceTask = mkPreQuantumCode (Task.evaluateExpressionTask sourceTask)

preQuantumFromPAExprTask-fuel : ∀ sourceTask →
  preQuantumFuel (preQuantumFromPAExprTask sourceTask) ≡ Task.evaluateExpressionTask sourceTask
preQuantumFromPAExprTask-fuel sourceTask = refl

preQuantumStep : PreQuantumCode → PreQuantumCode
preQuantumStep (mkPreQuantumCode zero) = mkPreQuantumCode zero
preQuantumStep (mkPreQuantumCode (suc fuelValue)) = mkPreQuantumCode fuelValue

preQuantumFuelAdapter : Core.FuelAdapter PreQuantumCode
preQuantumFuelAdapter =
  Core.mkFuelAdapter preQuantumFuel

preQuantumKernel : Kernel lzero lzero lzero
preQuantumKernel = Core.mkFuelKernel preQuantumFuelAdapter

runPreQuantumWithin : ℕ → PreQuantumCode → PreQuantumCode
runPreQuantumWithin = Fuel.FuelProfile.iter Fuel.NatFuel preQuantumStep

runPreQuantumWithin-observation : Def.FuelObservationLaw preQuantumFuel runPreQuantumWithin
runPreQuantumWithin-observation zero sourceCode = refl
runPreQuantumWithin-observation (suc budget) (mkPreQuantumCode zero) =
  trans
    (runPreQuantumWithin-observation budget (mkPreQuantumCode zero))
    (trans
      (Core.universalFuelAfter-active-halt-zero budget)
      (sym (Core.universalFuelAfter-successor-active-zero budget)))
runPreQuantumWithin-observation (suc budget) (mkPreQuantumCode (suc fuelValue)) =
  trans
    (runPreQuantumWithin-observation budget (mkPreQuantumCode fuelValue))
    (sym (Core.universalFuelAfter-active-suc budget fuelValue))

preQuantumToUniversal : KernelHom preQuantumKernel Core.universalKernel
preQuantumToUniversal = Core.mkFuelToUniversal preQuantumFuelAdapter
