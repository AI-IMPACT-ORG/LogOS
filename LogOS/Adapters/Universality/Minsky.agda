{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Adapters.Universality.Minsky where

-- Universality adapter: Minsky-style fuel kernel into the universal fuel kernel.
-- This file should expose exactly one canonical `FuelAdapter` value and the
-- obvious projections/readouts that downstream packs consume.

open import LogOS.Prelude
open import LogOS.Host.Nat using (ℕ; zero; suc)
open import LogOS.LT.Kernel using (Kernel; Code)
open import LogOS.LT.Hom using (KernelHom)
open import LogOS.Ports.Universality.Task using (PATask; PAExprTask; taskFuel; evaluateExpressionTask)
import LogOS.Ports.Universality.Fuel as Fuel

import LogOS.Ports.Universality.Core as Core
import LogOS.Ports.Universality.Definitional as Def

data MinskyCode : Set lzero where
  mkMinskyCode : ℕ → MinskyCode

minskyFuel : MinskyCode → ℕ
minskyFuel (mkMinskyCode fuel) = fuel

minskyFromPATask : PATask → MinskyCode
minskyFromPATask sourceTask = mkMinskyCode (taskFuel sourceTask)

minskyStep : MinskyCode → MinskyCode
minskyStep (mkMinskyCode zero) = mkMinskyCode zero
minskyStep (mkMinskyCode (suc fuel)) = mkMinskyCode fuel

minskyFuelAdapter : Core.FuelAdapter MinskyCode
minskyFuelAdapter =
  Core.mkFuelAdapter minskyFuel

minskyKernel : Kernel lzero lzero lzero
minskyKernel = Core.mkFuelKernel minskyFuelAdapter

runMinskyWithin : ℕ → MinskyCode → MinskyCode
runMinskyWithin = Fuel.FuelProfile.iter Fuel.NatFuel minskyStep

runMinskyWithin-observation : Def.FuelObservationLaw minskyFuel runMinskyWithin
runMinskyWithin-observation zero sourceCode = refl
runMinskyWithin-observation (suc budget) (mkMinskyCode zero) =
  trans
    (runMinskyWithin-observation budget (mkMinskyCode zero))
    (trans
      (Core.universalFuelAfter-active-halt-zero budget)
      (sym (Core.universalFuelAfter-successor-active-zero budget)))
runMinskyWithin-observation (suc budget) (mkMinskyCode (suc fuel)) =
  runMinskyWithin-observation budget (mkMinskyCode fuel)

minskyFromPATask-fuel : ∀ sourceTask →
  minskyFuel (minskyFromPATask sourceTask) ≡ taskFuel sourceTask
minskyFromPATask-fuel sourceTask = refl

minskyFromPAExprTask : PAExprTask → MinskyCode
minskyFromPAExprTask sourceTask = mkMinskyCode (evaluateExpressionTask sourceTask)

minskyFromPAExprTask-fuel : ∀ sourceTask →
  minskyFuel (minskyFromPAExprTask sourceTask) ≡ evaluateExpressionTask sourceTask
minskyFromPAExprTask-fuel sourceTask = refl

minskyToUniversal : KernelHom minskyKernel Core.universalKernel
minskyToUniversal = Core.mkFuelToUniversal minskyFuelAdapter
