{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Telemetry where

-- Telemetry contracts for agent sockets: observation-only ports on policies.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Boundary.Telemetry
open import LogOS.Boundary.Port using (_≈∂[_]_)
open import LogOS.Kernel using (Kernel)
import LogOS.Kernel.Endo as LKEndo
import LogOS.Ports.Semantic.Interoperability as Interop

open import LogOS.Packs.Agents.Socket.Core using (AgentSocket)
import LogOS.Packs.Agents.Learning.Core as LearningCore

module For
  {ℓ ℓTask ℓT : Level}
  {Sig  : LogOSSignature ℓ}
  {Q    : QAdapter ℓ}
  {Task : Set ℓTask}
  (Sock : AgentSocket Sig Q Task)
  (T : TelemetryTrace ℓT)
  where

  open AgentSocket Sock
  module L = LearningCore.For Sock
  open L using (LearningStep; learnStep; normalizeStep; learnStep≤close)
  open TelemetryTrace T using (Trace; _⊑T_; reflT; transT)

  record TelemetryContract : Set (lsuc (ℓ ⊔ ℓT)) where
    field
      port
        : BoundaryTelemetryPort
            Sig Q (Kernel.HWorld LK) (Kernel.BB LK) (Kernel.HTruth LK)
            boundaryIO T

    open BoundaryTelemetryPort port public
      using (observe-bnd; observe-bnd-mono; observe-bnd-respects)

    telemetry-step
      : ∀ (s : LearningStep) (p : Con_bnd)
      → _⊑T_ (observe-bnd p) (observe-bnd (learnStep s p))
    telemetry-step s p = observe-bnd-mono (LKEndo.ClosureStep.infl s p)

    -- Budgeted policies: a policy is within a trace budget if its telemetry
    -- lies below that budget.
    WithinBudget : Trace → Con_bnd → Set ℓT
    WithinBudget b c = _⊑T_ (observe-bnd c) b

    withinBudget-mono
      : ∀ {b b' c}
      → _⊑T_ b b'
      → WithinBudget b c
      → WithinBudget b' c
    withinBudget-mono b≤b' within = transT within b≤b'

    withinBudget-respects-≈∂
      : ∀ {b c d}
      → c ≈∂[ boundaryIO ] d
      → WithinBudget b c
      → WithinBudget b d
    withinBudget-respects-≈∂ eq within =
      let
        (_ , d≤c) = observe-bnd-respects eq
      in
      transT d≤c within

    -- Canonical budget witness: the observed trace of the learned policy.
    budgeted-step
      : ∀ (s : LearningStep) (p : Con_bnd)
      → WithinBudget (observe-bnd (learnStep s p)) (learnStep s p)
    budgeted-step _ _ = reflT

    -- Normalization increases telemetry (closure is inflationary).
    telemetry-close
      : ∀ (s : LearningStep) (p : Con_bnd)
      → _⊑T_ (observe-bnd (learnStep s p))
              (observe-bnd (learnStep (normalizeStep s) p))
    telemetry-close s p = observe-bnd-mono (learnStep≤close s p)

    -- Budget back-propagation: if the learned policy fits, so does the source.
    withinBudget-step-back
      : ∀ {b} (s : LearningStep) (p : Con_bnd)
      → WithinBudget b (learnStep s p)
      → WithinBudget b p
    withinBudget-step-back s p within =
      transT (telemetry-step s p) within

    withinBudget-close-back
      : ∀ {b} (s : LearningStep) (p : Con_bnd)
      → WithinBudget b (learnStep (normalizeStep s) p)
      → WithinBudget b (learnStep s p)
    withinBudget-close-back s p within =
      transT (telemetry-close s p) within

    -- Shareable budgeted learning: the shareable refinement on the canonical
    -- port preserves budget witnesses (by unfolding the shareable step).
    withinBudget-shareable-back
      : ∀ {b}
      → (mono : L.SatMonotone)
      → (s : LearningStep) (p : Con_bnd)
      → WithinBudget b
          (Interop.PortRefinement.map
             (L.shareableStep canonicalBoundaryPort mono s) p)
      → WithinBudget b p
    withinBudget-shareable-back mono s p within =
      withinBudget-step-back s p within
