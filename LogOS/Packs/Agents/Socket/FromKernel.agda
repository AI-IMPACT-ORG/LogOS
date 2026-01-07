{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Socket.FromKernel where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature; module LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Kernel using (Kernel; module Kernel)
open import LogOS.Kernel.LogicKernel using (LogicKernel)

open import LogOS.Kernel.LogicKernel.FromKernel as LKFromK using (asLogicKernel)
import LogOS.Computation.KernelUniversalProcess as KUP
import LogOS.Computation.SchemeCategory as Cat

open import LogOS.Packs.Agents.Socket.Ports using (AgentPorts)
open import LogOS.Packs.Agents.Socket.Contracts using (AgentContracts)
open import LogOS.Packs.Agents.Socket.Core using (AgentSocket)

-- Canonical construction: any (unguarded) `Kernel` yields a “kernel-as-process”
-- socket where frameworks are *choices* into the shared `CodeProcess` or
-- `BoundaryProcess`.

module For
  {ℓ ℓTask : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K   : Kernel Sig Q)
  (Task : Set ℓTask)
  where

  open Kernel K using (BB)
  open BulkBoundary BB using (Con_bnd)

  module KP = KUP.ForKernel K

  LK : LogicKernel Sig Q
  LK = LKFromK.asLogicKernel K

  -- Socket where the process state is *code* (Guard ∘ Body) and observation is `decode`.
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

  -- Socket where the process state is boundary constraints (Flow ∘ Body∂).
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
