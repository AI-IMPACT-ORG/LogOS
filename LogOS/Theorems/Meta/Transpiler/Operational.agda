{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.Transpiler.Operational where

-- Minimal operational semantics layer for kernel code, phrased as a small-step
-- function (`FlowCode`) and its n-step iteration.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel
import LogOS.Computation.Core as Comp

module For
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  where

  Code : Set ℓ
  Code = Kernel.Code K

  -- Small-step semantics: one kernel step on code.
  StepCode : Code → Code
  StepCode = FlowCode K

  CodeComputation : Comp.Computation Code
  CodeComputation =
    record
      { Step = StepCode
      ; Halts = λ _ → Topℓ
      }

  exec : ℕ → Code → Code
  exec n γ = Comp.iterate CodeComputation n γ

  Con∂ : Set ℓ
  Con∂ = BulkBoundary.Con_bnd (Kernel.BB K)

  -- Boundary small-step semantics: Flow ∘ Body∂.
  Step∂ : Con∂ → Con∂
  Step∂ c =
    Truth.GuardedCore.GuardedClosure.Flow (Kernel.GTruth K) (Kernel.Body∂ K c)

  BoundaryComputation : Comp.Computation Con∂
  BoundaryComputation =
    record
      { Step = Step∂
      ; Halts = λ _ → Topℓ
      }

  exec∂ : ℕ → Con∂ → Con∂
  exec∂ n c = Comp.iterate BoundaryComputation n c

  -- One-step simulation: decode commutes with the operational step.
  decode-step
    : ∀ γ
    → Kernel.decode K (StepCode γ) ≡ Step∂ (Kernel.decode K γ)
  decode-step = decode-FlowCode K

  -- n-step simulation: decode commutes with iterated execution.
  decode-exec
    : ∀ n γ
    → Kernel.decode K (exec n γ) ≡ exec∂ n (Kernel.decode K γ)
  decode-exec zero    γ = refl
  decode-exec (suc n) γ =
    trans
      (decode-exec n (StepCode γ))
      (cong (exec∂ n) (decode-step γ))
