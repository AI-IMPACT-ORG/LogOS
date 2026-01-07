{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Socket.FromGradedKernel where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature; module LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Kernel.Graded using (GradedKernel; module GradedKernel)
open import LogOS.Kernel.LogicKernel using (LogicKernel)

open import LogOS.Kernel.LogicKernel.FromGradedKernel as LKFromG using (asLogicKernel)
import LogOS.Computation.KernelUniversalProcess as KUP
import LogOS.Computation.SchemeCategory as Cat

open import LogOS.Packs.Agents.Socket.Ports using (AgentPorts)
open import LogOS.Packs.Agents.Socket.Contracts using (AgentContracts)
open import LogOS.Packs.Agents.Socket.Core using (AgentSocket)

-- Canonical construction: any `GradedKernel` yields a socket where the shared
-- process exposes *budgeted* computation (via the kernel’s `step-grade`).

module For
  {ℓ ℓTask : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K   : GradedKernel Sig Q)
  (Task : Set ℓTask)
  where

  open GradedKernel K using (BB)
  open BulkBoundary BB using (Con_bnd)

  module KP = KUP.ForGradedKernel K

  LK : LogicKernel Sig Q
  LK = LKFromG.asLogicKernel K

  mkCodeSocket
    : AgentPorts Sig
    → (LogOSSignature.Iface Sig → Con_bnd)
    → AgentContracts Sig
    → Cat.Choice Task KP.CodeProcess
    → AgentSocket Sig Q Task
  mkCodeSocket ports val∂ C choice =
    record
      { LK     = LK
      ; ports  = ports
      ; val∂   = val∂
      ; C      = C
      ; P      = KP.CodeProcess
      ; choice = choice
      }

  mkBoundarySocket
    : AgentPorts Sig
    → (LogOSSignature.Iface Sig → Con_bnd)
    → AgentContracts Sig
    → Cat.Choice Task KP.BoundaryProcess
    → AgentSocket Sig Q Task
  mkBoundarySocket ports val∂ C choice =
    record
      { LK     = LK
      ; ports  = ports
      ; val∂   = val∂
      ; C      = C
      ; P      = KP.BoundaryProcess
      ; choice = choice
      }
