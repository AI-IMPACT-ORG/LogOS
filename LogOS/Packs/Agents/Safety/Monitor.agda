{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Safety.Monitor where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)

open import LogOS.Kernel.LogicKernel using (LogicKernel; GTier)
import LogOS.Kernel.LogicKernel.Endo as LKEndo
open import LogOS.Kernel.LogicKernel.TensorEndo using (_⊗ᵣ_)

open import LogOS.Boundary.Port using (Respects≈∂[_])

open import LogOS.Packs.Agents.Socket.Core using (AgentSocket)
import LogOS.Packs.Agents.EndoSurface as EndoSurface

-- A “monitor” is a monotone endomap on boundary constraints.
--
-- We package monitors as `Endo` values so the existing endomap/refinement DSL
-- (composition, pointwise refinement, closure helpers) applies directly.

module For
  {ℓ ℓTask : Level}
  {Sig  : LogOSSignature ℓ}
  {Q    : QAdapter ℓ}
  {Task : Set ℓTask}
  (Sock : AgentSocket Sig Q Task)
  where

  open AgentSocket Sock

  module E = EndoSurface.For Sock

  Monitor : Set (lsuc ℓ)
  Monitor = E.Endomap

  RespectsObsEq : Monitor → Set ℓ
  RespectsObsEq F = Respects≈∂[ boundaryIO ] (E.apply F)

  private
    FlowAt : GTier.Step (LogicKernel.G LK) → Con_bnd → Con_bnd
    FlowAt g = GTier.Flow (LogicKernel.G LK) g

    flowEndoAt : GTier.Step (LogicKernel.G LK) → LKEndo.Endo LK
    flowEndoAt g =
      record
        { fn = FlowAt g
        ; mono = GTier.mono (LogicKernel.G LK)
        }

  -- One canonical monitor: “enforce safety by tensoring it in, then saturating”.
  --
  -- This is a design choice, not a theorem: it makes the intended usage explicit
  -- while remaining order-agnostic (preorder-safe).
  defaultMonitorAt : GTier.Step (LogicKernel.G LK) → Monitor
  defaultMonitorAt g =
    LKEndo._∘E_ (flowEndoAt g) (LK ⊗ᵣ SafetySem)

  -- Default choice: saturate at the kernel’s `sat` grade.
  defaultMonitor : Monitor
  defaultMonitor = defaultMonitorAt (GTier.sat (LogicKernel.G LK))
