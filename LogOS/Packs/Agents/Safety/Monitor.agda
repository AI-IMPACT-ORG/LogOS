{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Safety.Monitor where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary; ConPoset)
open import LogOS.Minimal.Adjunction using (MonoidalPoset)
open import LogOS.Algebra.ConAlg using (ConAlg)

open import LogOS.Kernel.LogicKernel using (LogicKernel; GTier)

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

  -- One canonical monitor: “enforce safety by tensoring it in, then saturating”.
  --
  -- This is a design choice, not a theorem: it makes the intended usage explicit
  -- while remaining order-agnostic (preorder-safe).
  defaultMonitorAt : GTier.Step (LogicKernel.G LK) → Monitor
  defaultMonitorAt g =
    record
      { fn = λ c → FlowAt g (ConAlg._⊗∂_ conAlg c SafetySem)
      ; mono = λ {x} {y} x≤y →
          let
            CP    = BulkBoundary.bnd (ConAlg.BB conAlg)
            refl∂ = ConPoset.refl CP {c = SafetySem}
            open MonoidalPoset (ConAlg.MBnd conAlg) renaming (mono⊗ to mono⊗∂)
            step⊗ = mono⊗∂ x≤y refl∂
          in
          GTier.mono (LogicKernel.G LK) {g = g} step⊗
      }

  -- Default choice: saturate at the kernel’s `sat` grade.
  defaultMonitor : Monitor
  defaultMonitor = defaultMonitorAt (GTier.sat (LogicKernel.G LK))

  -- Backwards-compatible name: read as “this monitor *aims to* enforce safety”.
  -- The pack does not claim this yields unconditional safety; any such claim
  -- must be stated as an explicit assumption/theorem in the surrounding model.
  enforceSafety : Monitor
  enforceSafety = defaultMonitor
