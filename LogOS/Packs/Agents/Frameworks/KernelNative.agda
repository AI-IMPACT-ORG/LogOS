{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
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
import LogOS.Kernel.FromGradedKernel as LKFromGraded

import LogOS.Packs.Agents.Frameworks.Core as Core
import LogOS.Computation.SchemeCategory as Cat
import LogOS.Computation.KernelUniversalProcess as KUP

-- Kernel-native frameworks: treat the kernel itself as the shared process.
--
-- Tasks are either:
-- - Code-level (Code → boundary meaning via decode), or
-- - Boundary-level (constraints evolve under Flow ∘ Body∂).

module ForKernel
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  (stepGrade : QAdapter.Scale Q)
  where

  open Kernel K using (Code; BB)

  Con_bnd : Set ℓ
  Con_bnd = ConPreorder.Con (BulkBoundary.bnd BB)

  module KP = KUP.ForKernel K stepGrade
  open KP

  codeInterface : (Code → ℕ) → Cat.Interface Code CodeProcess
  codeInterface fuel = record { compile = λ γ → γ ; fuel = fuel }

  codeFramework : (Code → ℕ) → Core.Framework Code Con_bnd CodeProcess
  codeFramework fuel = record { interface = codeInterface fuel }

  boundaryInterface : (Con_bnd → ℕ) → Cat.Interface Con_bnd BoundaryProcess
  boundaryInterface fuel = record { compile = λ c → c ; fuel = fuel }

  boundaryFramework : (Con_bnd → ℕ) → Core.Framework Con_bnd Con_bnd BoundaryProcess
  boundaryFramework fuel = record { interface = boundaryInterface fuel }

module ForLogicCore
  {ℓ : Level}
  (C : LogicCore {ℓ})
  where
  -- Default step grade is `QAdapter.e` (the unit grade embedded into the scale).
  module Base = ForKernel (LogicCore.K C) (QAdapter.e (LogicCore.Q C))
  open Base public

module ForGradedKernel
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  where
  module Base = ForKernel (LKFromGraded.asKernel K) (GradedKernel.step-grade K)
  open Base public
