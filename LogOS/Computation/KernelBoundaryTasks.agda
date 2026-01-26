{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Computation.KernelBoundaryTasks where

-- Kernel-driven “lax task” story:
--
-- A kernel’s boundary dynamics is typically given by a *raw* evolution `Body∂`
-- and a *closure* `Flow` (stable truth / saturation / canonicalization).
--
-- This module packages the observation that “raw evolution” factors *laxly*
-- through “Flow-saturated evolution”:
--
--   Body∂ c ⊑ Flow (Body∂ c)
--
-- and then lifts it to finite tasks via `LogOS.Computation.Tasks.TransportLax`.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (ConPreorder; BulkBoundary)
import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel using (Kernel)
import LogOS.Computation.Scheme as Sch
import LogOS.Computation.SchemeCategory as Cat

open import LogOS.Computation.Tasks

module ForKernel
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  where

  open Kernel K

  private
    CP∂ : ConPreorder ℓ
    CP∂ = BulkBoundary.bnd BB

    module CP∂ = ConPreorder CP∂

    Flow : CP∂.Con → CP∂.Con
    Flow = Truth.GuardedCore.GuardedClosure.Flow GTruth

    idClosure∂ : Sch.Closure CP∂
    idClosure∂ =
      record
        { cl        = λ c → c
        ; mono      = λ p → p
        ; infl      = λ _ → CP∂.refl
        ; idemp-lax = λ _ → CP∂.refl
        }

  -- Boundary evolution without applying Flow.
  RawBoundaryProcess : Cat.Process CP∂.Con
  RawBoundaryProcess =
    record
      { CP       = CP∂
      ; Step     = Body∂
      ; Close     = idClosure∂
      ; decode   = λ c → c
      ; Q        = Q
      ; stepCost = λ _ → QAdapter.e Q
      }

  -- Boundary evolution with Flow applied after each raw step.
  SatBoundaryProcess : Cat.Process CP∂.Con
  SatBoundaryProcess =
    record
      { CP       = CP∂
      ; Step     = λ c → Flow (Body∂ c)
      ; Close     = idClosure∂
      ; decode   = λ c → c
      ; Q        = Q
      ; stepCost = λ _ → QAdapter.e Q
      }

  satStepMono : Cat.StepMono SatBoundaryProcess
  satStepMono le = mono-Flow (mono-Body∂ le)

  raw→sat : Cat.ProcessHomLax RawBoundaryProcess SatBoundaryProcess
  raw→sat =
    record
      { map        = λ c → c
      ; mono       = λ le → le
      ; step-comm≤ = λ c → Truth.GuardedCore.GuardedClosure.infl GTruth (Body∂ c)
      ; norm-comm≤ = λ _ → CP∂.refl
      ; decode-comm = λ _ → refl
      }

  module TRaw = ForProcess RawBoundaryProcess
  module TSat = ForProcess SatBoundaryProcess

  module TLax = TRaw.TransportLax raw→sat satStepMono

  execFrom≤sat : ∀ n c → Cat.Process._⊑_ SatBoundaryProcess (TRaw.execFrom n c) (TSat.execFrom n c)
  execFrom≤sat n c = TLax.execFrom-map≤ n c

  nfFrom≤sat : ∀ n c → Cat.Process._⊑_ SatBoundaryProcess (TRaw.nfFrom n c) (TSat.nfFrom n c)
  nfFrom≤sat n c = TLax.nfFrom-map≤ n c

  nfTask≤sat : ∀ t → Cat.Process._⊑_ SatBoundaryProcess (TRaw.nfTask t) (TSat.nfTask t)
  nfTask≤sat t = TLax.nfTask-map≤ t
