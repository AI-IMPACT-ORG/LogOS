{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Adapters.Universality.Lambda where

-- Universality adapter: minimal λ-style fuel kernel into the universal fuel kernel.

open import LogOS.Prelude
open import LogOS.Host.Nat using (ℕ; zero; suc)
open import LogOS.LT.Kernel using (Kernel; Code)
open import LogOS.LT.Hom using (KernelHom)
open import LogOS.Ports.Universality.Task using (PATask; PAExprTask; taskFuel; evaluateExpressionTask)
import LogOS.Ports.Universality.Fuel as Fuel

import LogOS.Ports.Universality.Core as Core
import LogOS.Ports.Universality.Definitional as Def

data LambdaCode : Set lzero where
  mkLambdaDelay : ℕ → LambdaCode
  mkLambdaReady : ℕ → LambdaCode

lambdaFuel : LambdaCode → ℕ
lambdaFuel (mkLambdaDelay fuel) = fuel
lambdaFuel (mkLambdaReady fuel) = fuel

lambdaFromPATask : PATask → LambdaCode
lambdaFromPATask sourceTask = mkLambdaDelay (taskFuel sourceTask)

lambdaStep : LambdaCode → LambdaCode
lambdaStep (mkLambdaDelay zero) = mkLambdaReady zero
lambdaStep (mkLambdaDelay (suc fuel)) = mkLambdaReady fuel
lambdaStep (mkLambdaReady zero) = mkLambdaReady zero
lambdaStep (mkLambdaReady (suc fuel)) = mkLambdaReady fuel

lambdaFuelAdapter : Core.FuelAdapter LambdaCode
lambdaFuelAdapter =
  Core.mkFuelAdapter lambdaFuel

lambdaKernel : Kernel lzero lzero lzero
lambdaKernel = Core.mkFuelKernel lambdaFuelAdapter

runLambdaWithin : ℕ → LambdaCode → LambdaCode
runLambdaWithin = Fuel.FuelProfile.iter Fuel.NatFuel lambdaStep

runLambdaWithin-observation : Def.FuelObservationLaw lambdaFuel runLambdaWithin
runLambdaWithin-observation zero sourceCode = refl
runLambdaWithin-observation (suc budget) (mkLambdaDelay zero) =
  trans
    (runLambdaWithin-observation budget (mkLambdaReady zero))
    (trans
      (Core.universalFuelAfter-active-halt-zero budget)
      (sym (Core.universalFuelAfter-successor-active-zero budget)))
runLambdaWithin-observation (suc budget) (mkLambdaDelay (suc fuel)) =
  trans
    (runLambdaWithin-observation budget (mkLambdaReady fuel))
    (sym (Core.universalFuelAfter-active-suc budget fuel))
runLambdaWithin-observation (suc budget) (mkLambdaReady zero) =
  trans
    (runLambdaWithin-observation budget (mkLambdaReady zero))
    (trans
      (Core.universalFuelAfter-active-halt-zero budget)
      (sym (Core.universalFuelAfter-successor-active-zero budget)))
runLambdaWithin-observation (suc budget) (mkLambdaReady (suc fuel)) =
  runLambdaWithin-observation budget (mkLambdaReady fuel)

lambdaFromPATask-fuel : ∀ sourceTask →
  lambdaFuel (lambdaFromPATask sourceTask) ≡ taskFuel sourceTask
lambdaFromPATask-fuel sourceTask = refl

lambdaFromPAExprTask : PAExprTask → LambdaCode
lambdaFromPAExprTask sourceTask = mkLambdaDelay (evaluateExpressionTask sourceTask)

lambdaFromPAExprTask-fuel : ∀ sourceTask →
  lambdaFuel (lambdaFromPAExprTask sourceTask) ≡ evaluateExpressionTask sourceTask
lambdaFromPAExprTask-fuel sourceTask = refl

lambdaToUniversal : KernelHom lambdaKernel Core.universalKernel
lambdaToUniversal = Core.mkFuelToUniversal lambdaFuelAdapter
