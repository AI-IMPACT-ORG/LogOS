{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.EndoSurface where

-- Shared “agent endomap” vocabulary:
-- both monitoring and learning are endomaps on boundary constraints.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Boundary.IO using (BoundaryIO)

open import LogOS.Packs.Agents.Socket.Core using (AgentSocket)
import LogOS.Kernel.Shape as Core
open import LogOS.Kernel using (Kernel)
import LogOS.Kernel.Endo as LKEndo

module For
  {ℓ ℓTask : Level}
  {Sig  : LogOSSignature ℓ}
  {Q    : QAdapter ℓ}
  {Task : Set ℓTask}
  (Sock : AgentSocket Sig Q Task)
  where

  open LogOSSignature Sig using (Cosp; ∂Cosp; to∂)
  open AgentSocket Sock

  Policy : Set ℓ
  Policy = Con_bnd

  Endomap : Set (lsuc ℓ)
  Endomap = LKEndo.Endo LK

  apply : Endomap → Policy → Policy
  apply U = LKEndo.Endo.fn U

  ClosureStep : Set (lsuc ℓ)
  ClosureStep = LKEndo.ClosureStep LK

  applyStep : ClosureStep → Policy → Policy
  applyStep step = LKEndo.Endo.fn (LKEndo.ClosureStep.endo step)

  -- Boundary satisfaction for the socket.
  Sat : LogOSSignature.∂Cosp Sig → Con_bnd → Set ℓ
  Sat = BoundaryIO.Sat∂ (AgentSocket.boundaryIO Sock)

  -- Satisfaction is monotone w.r.t. boundary order.
  SatMonotone : Set _
  SatMonotone =
    ∀ {c d}
    → _⊑bnd_ c d
    → ∀ p → Sat p c → Sat p d

  -- A boundary endomap is satisfaction-preserving (sound).
  SatPreserving : (Con_bnd → Con_bnd) → Set _
  SatPreserving F = ∀ p c → Sat p c → Sat p (F c)

  -- Closure steps are sound if satisfaction is monotone.
  satPreserving-from-step
    : SatMonotone
    → (step : ClosureStep)
    → SatPreserving (applyStep step)
  satPreserving-from-step mono step p c sat =
    mono (LKEndo.ClosureStep.infl step c) p sat

  -- Kernel-aligned monotonicity: if the boundary contexts come from a section
  -- of `to∂`, monotonicity follows from the kernel coherence.
  satMonotone-from-kernel
    : (ctx : ∂Cosp → Cosp)
    → (ctx-to∂ : ∀ p → to∂ (ctx p) ≡ p)
    → SatMonotone
  satMonotone-from-kernel ctx ctx-to∂ {c} {d} c≤d p sat =
    let
      S = Kernel.shape LK

      sat' : Core.KernelShape.Sat_H_bnd S (to∂ (ctx p)) d
      sat' =
        Core.Sat_H_bnd-mono S {w = ctx p} c≤d
          (subst (λ q → Sat q c) (sym (ctx-to∂ p)) sat)
    in
    subst (λ q → Sat q d) (ctx-to∂ p) sat'
