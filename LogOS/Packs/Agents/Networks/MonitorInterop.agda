{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Networks.MonitorInterop where

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop

open import LogOS.Boundary.Port using (BoundaryPort)
open import LogOS.Kernel.LogicKernel using (LogicKernel; GTier)
open import LogOS.Kernel.LogicKernel.Endo as LKEndo
open import LogOS.Minimal.Truth as Truth
open import LogOS.Ports.Semantic.SatMor using (SatMor)

open import LogOS.Packs.Agents.Socket.Core using (AgentSocket)
open import LogOS.Packs.Agents.Networks.Hetero using (AgentNetwork)
import LogOS.Packs.Agents.Networks.Interop as Interop
import LogOS.Packs.Agents.Safety.Monitor as Monitor

-- Ported-closure naturality specialized to monitors:
-- edge translations commute with monitor application (up to satisfaction).
--
-- The compatibility lemma below is explicit about the hypotheses required for
-- the default monitor to commute across an edge (flow + tensor safety).

module For
  {ℓ ℓTask ℓRole : Level}
  {Role : Set ℓRole}
  (Net : AgentNetwork {ℓ} {ℓTask} Role)
  {r s : Role}
  (edge : AgentNetwork.Edge Net r s)
  {ℓFormR ℓFormS : Level}
  (PortR : BoundaryPort {ℓForm = ℓFormR} _ _ _ _ _
           (AgentSocket.boundaryIO (AgentNetwork.Sock Net r)))
  (PortS : BoundaryPort {ℓForm = ℓFormS} _ _ _ _ _
           (AgentSocket.boundaryIO (AgentNetwork.Sock Net s)))
  where

  open AgentNetwork Net

  module Inter = Interop.ForEquiv Net edge PortR PortS
  open Inter

  module MonR = Monitor.For (Sock r)
  module MonS = Monitor.For (Sock s)

  open AgentNetwork.Edge edge
  module M = SatMor satMor

  private
    LK_R : LogicKernel _ _
    LK_R = AgentSocket.LK (Sock r)

    LK_S : LogicKernel _ _
    LK_S = AgentSocket.LK (Sock s)

    flowR : Con r → Con r
    flowR c = GTier.Flow (LogicKernel.G LK_R) (GTier.sat (LogicKernel.G LK_R)) c

    flowS : Con s → Con s
    flowS c = GTier.Flow (LogicKernel.G LK_S) (GTier.sat (LogicKernel.G LK_S)) c

    tensorR : Con r → Con r → Con r
    tensorR = tensorAt r

    tensorS : Con s → Con s → Con s
    tensorS = tensorAt s

    safetyR : Con r
    safetyR = AgentSocket.SafetySem (Sock r)

    safetyS : Con s
    safetyS = AgentSocket.SafetySem (Sock s)

  applyR : MonR.Monitor → Con r → Con r
  applyR M = LKEndo.Endo.fn M

  applyS : MonS.Monitor → Con s → Con s
  applyS M = LKEndo.Endo.fn M

  monitor-translate-commutes
    : ∀ (MR : MonR.Monitor) (MS : MonS.Monitor)
    → RespectsObsEq₂↑ (applyS MS)
    → Compatible (applyR MR) (applyS MS)
    → ∀ p (φ : BoundaryPort.Form PortR)
    → Prop._↔_ (SatF₂↑ p (translate (Extend₁ (applyR MR) φ)))
               (SatF₂↑ p (Extend₂ (applyS MS) (translate φ)))
  monitor-translate-commutes MR MS ext compat p φ =
    ported-closure-naturality (applyR MR) (applyS MS) ext compat p φ

  -- μ-level strengthening: exported Kleene μ fixed points transport across the edge.
  --
  -- This is the limit-level analogue of `monitor-translate-commutes`, but it
  -- talks about a distinguished stabilised constraint (μ) rather than a single
  -- application of `Extend`.
  module LimitMu where
    open Inter.Limit public using (MuTransportData; MuTransportData↑; translate-μ≤; translate-μ≤↑)

    monitor-translate-μ≤
      : ∀ {ω₁ ω₂}
        (MR : MonR.Monitor) (MS : MonS.Monitor)
      → MuTransportData ω₁ ω₂ (applyR MR) (applyS MS)
      → ∀ p
      → SatF₂↑ p (translate (BoundaryPort.Interp PortR (Truth.GuardedCore.Kleene.μ ω₁ (applyR MR))))
      → SatF₂↑ p (BoundaryPort.Interp PortS (Truth.GuardedCore.Kleene.μ ω₂ (applyS MS)))
    monitor-translate-μ≤ {ω₁ = ω₁} {ω₂ = ω₂} MR MS A p sat =
      translate-μ≤ {ω₁ = ω₁} {ω₂ = ω₂} A p sat

    monitor-translate-μ≤↑
      : ∀ {ω₁ ω₂}
        (MR : MonR.Monitor) (MS : MonS.Monitor)
      → MuTransportData↑ ω₁ ω₂ (applyR MR) (applyS MS)
      → ∀ p
      → SatF₂↑ p (translate (BoundaryPort.Interp PortR (Truth.GuardedCore.Kleene.μ ω₁ (applyR MR))))
      → SatF₂↑ p (BoundaryPort.Interp PortS (Truth.GuardedCore.Kleene.μ ω₂ (applyS MS)))
    monitor-translate-μ≤↑ {ω₁ = ω₁} {ω₂ = ω₂} MR MS A p sat =
      translate-μ≤↑ {ω₁ = ω₁} {ω₂ = ω₂} A p sat

    monitor-preserves-stabilisation≤ = monitor-translate-μ≤
    monitor-preserves-stabilisation≤↑ = monitor-translate-μ≤↑

  -- Default monitor compatibility for edges that commute with flow and tensor.
  defaultMonitor-compatible
    : RespectsObsEq₂↑ flowS
    → (flowCompat : ∀ c → Prop.ObsEqOn M.Sat₂↑ (translateCon (flowR c))
                                       (flowS (translateCon c)))
    → (tensorCompatSafety
        : ∀ c → Prop.ObsEqOn M.Sat₂↑
                 (translateCon (tensorR c safetyR))
                 (tensorS (translateCon c) safetyS))
    → Compatible (applyR MonR.defaultMonitor) (applyS MonS.defaultMonitor)
  defaultMonitor-compatible flowRespects flowCompat tensorCompatSafety =
    compatible-comp
      {F₁ = flowR}
      {G₁ = λ c → tensorR c safetyR}
      {F₂ = flowS}
      {G₂ = λ c → tensorS c safetyS}
      flowRespects
      (record { commute = flowCompat })
      (record { commute = tensorCompatSafety })
