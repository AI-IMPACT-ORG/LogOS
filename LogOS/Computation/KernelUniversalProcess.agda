{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Computation.KernelUniversalProcess where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con using (ConPreorder; BulkBoundary)

open import LogOS.Kernel.Graded using (GradedKernel)
import LogOS.Kernel.Shape as Core
open import LogOS.Kernel using (Kernel; GTier; BoxAt; BoxClosure; SatClosure; decode-Box; decode-BoxAt)
import LogOS.Kernel.FromGradedKernel as LKFromGraded

import LogOS.Computation.Scheme as Sch
import LogOS.Computation.SchemeCategory as Cat

-- Kernel-as-process: expose the kernel’s canonical computation in two layers:
--
-- 1) Code process: state = `Kernel.Code`, step = “compute then stabilise”
--    (`BoxAt step (Body _)`),
--    observation = `decode`.
-- 2) Boundary process: state = boundary constraints, step = `Flow ∘ Body∂`,
--    observation = identity.
--
-- The key link is definitional/explicit: `decode` transports the code step into
-- the boundary step via `decode-BoxAt` + `body-decode`.

module ForKernel
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  (stepGrade : QAdapter.Scale Q)
  where

  open Kernel K

  private
    CP∂ : ConPreorder ℓ
    CP∂ = BulkBoundary.bnd BB

    module CP∂ = ConPreorder CP∂

    step∂ : CP∂.Con → CP∂.Con
    step∂ c = GTier.Flow (Kernel.G K) (GTier.step (Kernel.G K)) (Body∂ c)

    -- Code carrier with the kernel refinement preorder (decode into boundary constraints).
    CPCode : ConPreorder ℓ
    CPCode = Core.CodePreorder (Kernel.shape K)

  BoundaryProcess : Cat.Process CP∂.Con
  BoundaryProcess =
    record
      { CP       = CP∂
      ; Step     = step∂
      ; Close     = SatClosure K
      ; decode   = λ c → c
      ; Q        = Q
      ; stepCost = λ _ → stepGrade
      }

  CodeProcess : Cat.Process CP∂.Con
  CodeProcess =
    record
      { CP       = CPCode
      ; Step     = λ γ → BoxAt K (GTier.step (Kernel.G K)) (Body γ)
      ; Close     = BoxClosure K
      ; decode   = decode
      ; Q        = Q
      ; stepCost = λ _ → stepGrade
      }

  decodeHom : Cat.ProcessHom CodeProcess BoundaryProcess
  decodeHom =
    record
      { map = decode
      ; mono = λ le → le
      ; step-comm = λ γ →
          let
            FlowStep : CP∂.Con → CP∂.Con
            FlowStep = GTier.Flow (Kernel.G K) (GTier.step (Kernel.G K))

            step₁ : decode (BoxAt K (GTier.step (Kernel.G K)) (Body γ)) ≡ FlowStep (decode (Body γ))
            step₁ = decode-BoxAt K (GTier.step (Kernel.G K)) (Body γ)

            step₂ : decode (Body γ) ≡ Body∂ (decode γ)
            step₂ = body-decode γ
          in
          trans step₁ (cong FlowStep step₂)
      ; norm-comm = decode-Box K
      ; decode-comm = λ _ → refl
      }

  decodeHomLax : Cat.ProcessHomLax CodeProcess BoundaryProcess
  decodeHomLax = Cat.ProcessHom→Lax decodeHom

-- Graded kernel-as-process: same story as `ForKernel`, but boundary evolution is
-- driven by the graded flow at the kernel’s chosen step grade (not necessarily
-- saturation). This makes “budgeted/graded computation” explicit at the process
-- level.

module ForGradedKernel {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} (K : GradedKernel Sig Q) where

  module LK = ForKernel (LKFromGraded.asKernel K) (GradedKernel.step-grade K)
  open LK public
