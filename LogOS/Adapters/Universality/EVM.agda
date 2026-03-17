{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Adapters.Universality.EVM where

-- Universality adapter: EVM-style fuel kernel into the universal fuel kernel.

open import LogOS.Prelude
open import LogOS.LT.Kernel using (Kernel; Code)
open import LogOS.LT.Hom using (KernelHom)
import LogOS.Ports.Universality.Fuel as Fuel

import LogOS.Ports.Universality.Core as Core
import LogOS.Ports.Universality.Definitional as Def
import LogOS.Ports.Universality.Task as Task

data EVMCode : Set lzero where
  mkEVMCode : ℕ → EVMCode

evmFuel : EVMCode → ℕ
evmFuel (mkEVMCode fuelValue) = fuelValue

evmFromPATask : Task.PATask → EVMCode
evmFromPATask sourceTask = mkEVMCode (Task.taskFuel sourceTask)

evmFromPATask-fuel : ∀ sourceTask →
  evmFuel (evmFromPATask sourceTask) ≡ Task.taskFuel sourceTask
evmFromPATask-fuel sourceTask = refl

evmFromPAExprTask : Task.PAExprTask → EVMCode
evmFromPAExprTask sourceTask = mkEVMCode (Task.evaluateExpressionTask sourceTask)

evmFromPAExprTask-fuel : ∀ sourceTask →
  evmFuel (evmFromPAExprTask sourceTask) ≡ Task.evaluateExpressionTask sourceTask
evmFromPAExprTask-fuel sourceTask = refl

evmStep : EVMCode → EVMCode
evmStep (mkEVMCode zero) = mkEVMCode zero
evmStep (mkEVMCode (suc fuelValue)) = mkEVMCode fuelValue

evmFuelAdapter : Core.FuelAdapter EVMCode
evmFuelAdapter =
  Core.mkFuelAdapter evmFuel

evmKernel : Kernel lzero lzero lzero
evmKernel = Core.mkFuelKernel evmFuelAdapter

runEVMWithin : ℕ → EVMCode → EVMCode
runEVMWithin = Fuel.FuelProfile.iter Fuel.NatFuel evmStep

runEVMWithin-observation : Def.FuelObservationLaw evmFuel runEVMWithin
runEVMWithin-observation zero sourceCode = refl
runEVMWithin-observation (suc budget) (mkEVMCode zero) =
  trans
    (runEVMWithin-observation budget (mkEVMCode zero))
    (trans
      (Core.universalFuelAfter-active-halt-zero budget)
      (sym (Core.universalFuelAfter-successor-active-zero budget)))
runEVMWithin-observation (suc budget) (mkEVMCode (suc fuelValue)) =
  trans
    (runEVMWithin-observation budget (mkEVMCode fuelValue))
    (sym (Core.universalFuelAfter-active-suc budget fuelValue))

evmToUniversal : KernelHom evmKernel Core.universalKernel
evmToUniversal = Core.mkFuelToUniversal evmFuelAdapter
