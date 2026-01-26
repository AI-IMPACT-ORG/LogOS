{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Frameworks.KernelNative where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (ConPreorder; BulkBoundary)

open import LogOS.API.Assumptions.Core using (LogicCore)

open import LogOS.Kernel using (Kernel)
open import LogOS.Kernel.Graded using (GradedKernel)
open import LogOS.Kernel.LogicKernel using (LogicKernel)
import LogOS.Kernel.LogicKernel.FromKernel as LKFromKernel
import LogOS.Kernel.LogicKernel.FromGradedKernel as LKFromGraded

import LogOS.Packs.Agents.Frameworks.Core as Core
import LogOS.Computation.SchemeCategory as Cat
import LogOS.Computation.KernelUniversalProcess as KUP

-- Kernel-native frameworks: treat the kernel itself as the shared process.
--
-- Tasks are either:
-- - Code-level (Code → boundary meaning via decode), or
-- - Boundary-level (constraints evolve under Flow ∘ Body∂).

module ForLogicKernel
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : LogicKernel Sig Q)
  (stepGrade : QAdapter.Scale Q)
  where

  open LogicKernel K using (Code; BB)

  Con_bnd : Set ℓ
  Con_bnd = ConPreorder.Con (BulkBoundary.bnd BB)

  module KP = KUP.ForLogicKernel K stepGrade
  open KP

  codeChoice : (Code → ℕ) → Cat.Choice Code CodeProcess
  codeChoice fuel = record { compile = λ γ → γ ; fuel = fuel }

  codeFramework : (Code → ℕ) → Core.Framework Code Con_bnd CodeProcess
  codeFramework fuel = record { choice = codeChoice fuel }

  boundaryChoice : (Con_bnd → ℕ) → Cat.Choice Con_bnd BoundaryProcess
  boundaryChoice fuel = record { compile = λ c → c ; fuel = fuel }

  boundaryFramework : (Con_bnd → ℕ) → Core.Framework Con_bnd Con_bnd BoundaryProcess
  boundaryFramework fuel = record { choice = boundaryChoice fuel }

module ForLogicCore
  {ℓ : Level}
  (C : LogicCore {ℓ})
  where
  -- Default step grade is `QAdapter.e` (the unit grade embedded into the scale).
  module Base = ForLogicKernel (LogicCore.K C) (QAdapter.e (LogicCore.Q C))
  open Base public

module ForKernel
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  where
  module Base = ForLogicKernel (LKFromKernel.asLogicKernel K) (QAdapter.e Q)
  open Base public

module ForGradedKernel
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  where
  module Base = ForLogicKernel (LKFromGraded.asLogicKernel K) (GradedKernel.step-grade K)
  open Base public
