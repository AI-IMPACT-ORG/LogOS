{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Learning.Network where

-- Learning across sound network edges:
-- a sound edge translation composes with learning refinements to yield a
-- sound refinement of the edge itself.

open import LogOS.Prelude

open import LogOS.Boundary.IO using (BoundaryIO)
open import LogOS.Boundary.Port using (BoundaryPort)
open import LogOS.Ports.Semantic.Interlingua using (toPresentationC)
open import LogOS.Ports.Semantic.SatMor using (idSatHom)
import LogOS.Ports.Semantic.Interoperability as Interop

open import LogOS.Packs.Agents.Socket.Core using (AgentSocket)
open import LogOS.Packs.Agents.Networks.Hetero using (AgentNetwork)
import LogOS.Packs.Agents.Networks.Interop as NetInterop
import LogOS.Packs.Agents.Learning.Core as LearningCore

module For
  {ℓ ℓTask ℓRole : Level}
  {Role : Set ℓRole}
  (Net : AgentNetwork {ℓ} {ℓTask} Role)
  {r s : Role}
  (edge : AgentNetwork.EdgeSound Net r s)
  {ℓFormR ℓFormS : Level}
  (PortR : BoundaryPort {ℓForm = ℓFormR} _ _ _ _ _
           (AgentSocket.boundaryIO (AgentNetwork.Sock Net r)))
  (PortS : BoundaryPort {ℓForm = ℓFormS} _ _ _ _ _
           (AgentSocket.boundaryIO (AgentNetwork.Sock Net s)))
  where

  open AgentNetwork Net

  module Inter = NetInterop.For Net edge PortR PortS
  open Inter

  module LR = LearningCore.For (Sock r)
  module LS = LearningCore.For (Sock s)

  private
    SockR = Sock r
    SockS = Sock s

    BR = AgentSocket.boundaryIO SockR
    BS = AgentSocket.boundaryIO SockS

    PR = toPresentationC BR PortR
    PS = toPresentationC BS PortS
    m = AgentNetwork.EdgeSound.satHom edge

  -- Learn after translating along the edge (target-side learning).
  refineAfter
    : EdgeRefinement
    → LS.LearningRefinement PortS
    → EdgeRefinement
  refineAfter edgeRef learnRef =
    let
      learnRefH = Interop.boundaryRefinementToHetero BS learnRef
    in
    Interop.heteroComposeRefinement
      m (idSatHom (BoundaryIO.Sat∂ BS)) PR PS PS edgeRef learnRefH

  -- Learn before translating along the edge (source-side learning).
  refineBefore
    : LR.LearningRefinement PortR
    → EdgeRefinement
    → EdgeRefinement
  refineBefore learnRef edgeRef =
    let
      learnRefH = Interop.boundaryRefinementToHetero BR learnRef
    in
    Interop.heteroComposeRefinement
      (idSatHom (BoundaryIO.Sat∂ BR)) m PR PR PS learnRefH edgeRef

  -- Shareable learning steps: choose a sound step and transport it as a
  -- refinement across the edge (reproducible learning).

  shareAfterStep
    : EdgeRefinement
    → LS.SatMonotone
    → LS.LearningStep
    → EdgeRefinement
  shareAfterStep edgeRef mono step =
    refineAfter edgeRef (LS.shareableStep PortS mono step)

  shareBeforeStep
    : LR.SatMonotone
    → LR.LearningStep
    → EdgeRefinement
    → EdgeRefinement
  shareBeforeStep mono step edgeRef =
    refineBefore (LR.shareableStep PortR mono step) edgeRef
