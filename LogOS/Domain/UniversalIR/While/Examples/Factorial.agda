{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.While.Examples.Factorial where

open import LogOS.Prelude

open import LogOS.Domain.UniversalIR.Core
open import LogOS.Domain.UniversalIR.Universality using (simulateUM; simulateUE)
open import LogOS.Domain.UniversalIR.IR using (observe)
import LogOS.Computation.Scheme as Sch
import LogOS.Computation.SchemeCategory as Cat
open import LogOS.Domain.UniversalIR.Schemes using (MinskyProcess; EthereumProcess)
open import LogOS.Domain.UniversalIR.While.Compile
open import LogOS.Domain.UniversalIR.While.Theorems using (fact; fuelFactM; minsky-factorial-correct)
import LogOS.Domain.UniversalIR.Theorems as UThm

-- EXAMPLE (argument): certified compilation runs for a concrete program (factorial).

-- Simple EVM step budget for factorial: init (6) + n iterations (19 each) + exit (8).
fuelFactE : ℕ → ℕ
fuelFactE n = 6 + (19 * n) + 8

-- Non-trivial concrete example: factorial 5 = 120 across Minsky and EVM.

n₅ : ℕ
n₅ = 5

fact₅ : ℕ
fact₅ = fact n₅

fact₅≡120 : fact₅ ≡ 120
fact₅≡120 = refl

outM₅ : ℕ
outM₅ = observe (simulate (fuelFactM n₅) (UM (compileMinsky (mkFact n₅))))

-- The same computation, rebased to the Scheme view (machine = process + choice).

fuelM : FactTask → ℕ
fuelM t = fuelFactM (FactTask.n t)

choiceM : Cat.Choice FactTask MinskyProcess
choiceM = record { compile = compileMinsky ; fuel = fuelM }

schemeM : Sch.Scheme FactTask ℕ
schemeM = Cat.schemeFromChoice MinskyProcess choiceM

schemeM≡observeSim : ∀ n → Sch.run schemeM (mkFact n) ≡ observe (simulate (fuelFactM n) (UM (compileMinsky (mkFact n))))
schemeM≡observeSim n =
  let fuel = fuelFactM n in
  let m    = compileMinsky (mkFact n) in
  let C    = Sch.Scheme.Comp schemeM in
  trans
    (cong (λ m' → observe (UM m')) (UThm.iterate≡iter C fuel m))
    (cong observe (sym (simulateUM fuel m)))

outM₅≡120 : outM₅ ≡ 120
outM₅≡120 =
  trans
    (minsky-factorial-correct n₅)
    fact₅≡120

outE₅ : ℕ
outE₅ = observe (simulate (fuelFactE n₅) (UE (compileEthereum (mkFact n₅))))

fuelE : FactTask → ℕ
fuelE t = fuelFactE (FactTask.n t)

choiceE : Cat.Choice FactTask EthereumProcess
choiceE = record { compile = compileEthereum ; fuel = fuelE }

schemeE : Sch.Scheme FactTask ℕ
schemeE = Cat.schemeFromChoice EthereumProcess choiceE

schemeE≡observeSim : ∀ n → Sch.run schemeE (mkFact n) ≡ observe (simulate (fuelFactE n) (UE (compileEthereum (mkFact n))))
schemeE≡observeSim n =
  let fuel = fuelFactE n in
  let e    = compileEthereum (mkFact n) in
  let C    = Sch.Scheme.Comp schemeE in
  trans
    (cong (λ e' → observe (UE e')) (UThm.iterate≡iter C fuel e))
    (cong observe (sym (simulateUE fuel e)))

-- This is a pure normalization check of the concrete compiled EVM code.
outE₅≡120 : outE₅ ≡ 120
outE₅≡120 = refl

outM₅≡outE₅ : outM₅ ≡ outE₅
outM₅≡outE₅ = trans outM₅≡120 (sym outE₅≡120)
