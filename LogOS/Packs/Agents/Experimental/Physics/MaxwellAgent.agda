{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Physics.MaxwellAgent where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Kernel using (Kernel)
open import LogOS.Boundary.Telemetry using (TelemetryTrace; ProgramTelemetryPort)

open import LogOS.Packs.Agents.Socket.Core using (AgentSocket)
import LogOS.Packs.Complexity.Experimental.PhysicsOfInformation as POI
open import LogOS.Complexity.MeasurementCapacity as MC

-- Maxwell agent surface: an agent socket plus physics-of-information primitives.

module For
  {ℓ ℓTask : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  {Task : Set ℓTask}
  (S : AgentSocket Sig Q Task)
  where

  open AgentSocket S

  LandauerForSocket : Set (lsuc (lsuc ℓ))
  LandauerForSocket =
    POI.LandauerIOAssumptions Sig Q (Kernel.HWorld LK) (Kernel.BB LK)
      (Kernel.HTruth LK) boundaryIO

  record MaxwellAgent (ℓT : Level) : Set (lsuc (lsuc (ℓ ⊔ ℓT))) where
    field
      landauer : LandauerForSocket
      capacity : MC.MeasurementCapacity Sig Q
      telemetry : TelemetryTrace ℓT
      programTelemetry
        : ProgramTelemetryPort
            Sig Q (Kernel.HWorld LK) (Kernel.BB LK) (Kernel.HTruth LK)
            boundaryIO telemetry
      capacityBridge
        : MC.TelemetryCapacityBridge
            Sig Q boundaryIO telemetry programTelemetry capacity

  open MaxwellAgent public
