{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Learning.Core where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature; module LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Boundary.Port using (BoundaryPort)
open import LogOS.Syntax.Prop as Prop

open import LogOS.Packs.Agents.Socket.Core using (AgentSocket)
import LogOS.Kernel.LogicKernel.Endo as LKEndo
import LogOS.Packs.Agents.EndoSurface as EndoSurface
import LogOS.Ports.Semantic.Interoperability as Interop

-- Learning is expressed in the same DSL as monitoring:
-- a policy is a boundary constraint, and a learning update is a monotone endomap.

module For
  {ℓ ℓTask : Level}
  {Sig  : LogOSSignature ℓ}
  {Q    : QAdapter ℓ}
  {Task : Set ℓTask}
  (S : AgentSocket Sig Q Task)
  where

  open AgentSocket S using (_⊑bnd_)
  module E = EndoSurface.For S

  Policy : Set ℓ
  Policy = E.Policy

  Update : Set (lsuc ℓ)
  Update = E.Endomap

  apply : Update → Policy → Policy
  apply = E.apply

  -- A “learning step” is a closure step (id ≤ update ≤ Flow),
  -- so it can be composed and reasoned about via the endomap DSL.
  LearningStep : Set (lsuc ℓ)
  LearningStep = E.ClosureStep

  learnStep : LearningStep → Policy → Policy
  learnStep = E.applyStep

  LK = AgentSocket.LK S

  -- Canonical closure of a learning step (apply, then Flow-shadow).
  normalizeStep : LearningStep → LearningStep
  normalizeStep = LKEndo.Flow-closeStep LK

  SatMonotone : Set _
  SatMonotone = E.SatMonotone

  SatPreserving : (Policy → Policy) → Set _
  SatPreserving = E.SatPreserving

  -- Closure-style: id ≤ step ≤ Flow.

  Flow : Policy → Policy
  Flow = LKEndo.Endo.fn (LKEndo.Flow-Endo LK)

  learnStep-infl
    : (s : LearningStep) (p : Policy)
    → _⊑bnd_ p (learnStep s p)
  learnStep-infl s p = LKEndo.ClosureStep.infl s p

  learnStep≤Flow
    : (s : LearningStep) (p : Policy)
    → _⊑bnd_ (learnStep s p) (Flow p)
  learnStep≤Flow s p = LKEndo.ClosureStep.leFlow s p

  -- Normalization strengthens a step (closure operator inflation).
  learnStep≤close
    : (s : LearningStep) (p : Policy)
    → _⊑bnd_ (learnStep s p) (learnStep (normalizeStep s) p)
  learnStep≤close s p = LKEndo.id≤Flow LK (learnStep s p)

  -- Normalization is idempotent (closure operator stability).
  normalizeStep-idempotent
    : (s : LearningStep) (p : Policy)
    → _⊑bnd_ (learnStep (normalizeStep (normalizeStep s)) p)
             (learnStep (normalizeStep s) p)
  normalizeStep-idempotent s p = LKEndo.Flow∘Flow≤Flow LK (learnStep s p)

  -- Learning as a sound refinement on a boundary port.
  --
  -- This is intentionally one-way: learning steps strengthen constraints
  -- without assuming reflectivity.

  B = AgentSocket.boundaryIO S

  LearningRefinement
    : ∀ {ℓForm : Level}
    → BoundaryPort {ℓForm = ℓForm} Sig Q _ _ _ B
    → Set _
  LearningRefinement P = Interop.PortRefinement B P P

  ObsLeF
    : ∀ {ℓForm : Level}
    → (P : BoundaryPort {ℓForm = ℓForm} Sig Q _ _ _ B)
    → BoundaryPort.Form P → BoundaryPort.Form P → Set _
  ObsLeF P = Prop.ObsLeOn (BoundaryPort.SatF P)

  refineWith
    : ∀ {ℓForm : Level}
    → (P : BoundaryPort {ℓForm = ℓForm} Sig Q _ _ _ B)
    → (F : Policy → Policy)
    → SatPreserving F
    → LearningRefinement P
  refineWith P F pres =
    record
      { map = BoundaryPort.Extend P F
      ; preserves-Sat = BoundaryPort.Extend-preserves-Sat P F pres
      }

  refineStep
    : ∀ {ℓForm : Level}
    → (P : BoundaryPort {ℓForm = ℓForm} Sig Q _ _ _ B)
    → SatMonotone
    → LearningStep
    → LearningRefinement P
  refineStep P mono step =
    refineWith P (learnStep step) (E.satPreserving-from-step mono step)

  -- Shareable learning: once boundary satisfaction is monotone, every learning
  -- step yields a refinement for any boundary port (shareable/reproducible).
  shareableStep
    : ∀ {ℓForm : Level}
    → (P : BoundaryPort {ℓForm = ℓForm} Sig Q _ _ _ B)
    → SatMonotone
    → LearningStep
    → LearningRefinement P
  shareableStep = refineStep

  -- Reproducible learning: refinements are observationally strengthening.
  refinement-strengthens
    : ∀ {ℓForm : Level}
    → (P : BoundaryPort {ℓForm = ℓForm} Sig Q _ _ _ B)
    → (R : LearningRefinement P)
    → (φ : BoundaryPort.Form P)
    → ObsLeF P φ (Interop.PortRefinement.map R φ)
  refinement-strengthens P R φ p sat =
    Interop.PortRefinement.preserves-Sat R p φ sat

  satMonotone-from-kernel
    : (ctx : LogOSSignature.∂Cosp Sig → LogOSSignature.Cosp Sig)
    → (ctx-to∂ : ∀ p → LogOSSignature.to∂ Sig (ctx p) ≡ p)
    → SatMonotone
  satMonotone-from-kernel = E.satMonotone-from-kernel

  learnStep-sound
    : ∀ {ℓForm : Level}
    → (P : BoundaryPort {ℓForm = ℓForm} Sig Q _ _ _ B)
    → (mono : SatMonotone)
    → (s : LearningStep)
    → ∀ p φ
    → BoundaryPort.SatF P p φ
    → BoundaryPort.SatF P p (Interop.PortRefinement.map (refineStep P mono s) φ)
  learnStep-sound P mono s p φ =
    Interop.PortRefinement.preserves-Sat (refineStep P mono s) p φ
