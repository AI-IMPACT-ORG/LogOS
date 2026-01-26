{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.ArbitraryTasks where

-- “Arbitrary tasks” for UniversalIR:
--
-- Instead of picking a small input language (like `PATask`) and writing
-- compilers, treat *the UniversalIR code itself* as the task language.
-- A task is then “run this `UCode` for `fuel` steps and observe it”.
--
-- This module also shows how a concrete paradigm (Minsky) embeds as a special
-- case by injection into `UCode`.

open import LogOS.Prelude

open import LogOS.Computation.Tasks public using (Fuelled; mkFuelled; fuel; payload; mapFuelled)

open import LogOS.Domain.UniversalIR.Core using
  ( UCode
  ; UM
  ; MinskyCode
  ; stepM
  ; simulate
  ; r0
  )
open import LogOS.Domain.UniversalIR.IR using (observe)
open import LogOS.Domain.UniversalIR.Std using (decodeChurch-church)
open import LogOS.Domain.UniversalIR.Universality using (simulateUM)
open import LogOS.Computation.Core using (iterateStep)

runFuelled : ∀ {ℓ} {A : Set ℓ} → (A → UCode) → Fuelled A → ℕ
runFuelled inject t = observe (simulate (fuel t) (inject (payload t)))

-- Universal tasks: `UCode` is the task language.

UCodeTask : Set
UCodeTask = Fuelled UCode

runUCodeTask : UCodeTask → ℕ
runUCodeTask = runFuelled (λ u → u)

-- Minsky as an example: a Minsky code is a task; execute it by injecting into `UCode`.

MinskyTask : Set
MinskyTask = Fuelled MinskyCode

embedMinskyTask : MinskyTask → UCodeTask
embedMinskyTask = mapFuelled UM

runMinskyTask : MinskyTask → ℕ
runMinskyTask = runFuelled UM

runMinskyTask≡runUCodeTask
  : ∀ t → runMinskyTask t ≡ runUCodeTask (embedMinskyTask t)
runMinskyTask≡runUCodeTask _ = refl

-- Sanity: under the canonical observation (`observe : UCode → ℕ`),
-- the Minsky branch reads out register `r0` after lowering to the IR.

observe-UM : ∀ m → observe (UM m) ≡ r0 m
observe-UM m = decodeChurch-church (r0 m)

runMinsky-fuel≡r0
  : ∀ fuel m → runMinskyTask (mkFuelled fuel m) ≡ r0 (iterateStep stepM fuel m)
runMinsky-fuel≡r0 fuel m =
  trans
    (cong observe (simulateUM fuel m))
    (observe-UM (iterateStep stepM fuel m))
