{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Socket.FromLogicKernel where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature; module LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Kernel.LogicKernel using (LogicKernel)

import LogOS.Computation.KernelUniversalProcess as KUP
import LogOS.Computation.SchemeCategory as Cat

open import LogOS.Packs.Agents.Socket.Ports using (AgentPorts)
open import LogOS.Packs.Agents.Socket.Contracts using (AgentContracts)
open import LogOS.Packs.Agents.Socket.Core using (AgentSocket)

-- Canonical construction: any `LogicKernel` yields a socket parameterized by a
-- chosen step grade, exposing code or boundary processes.

module For
  {ℓ ℓTask : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K   : LogicKernel Sig Q)
  (stepGrade : QAdapter.Scale Q)
  (Task : Set ℓTask)
  where

  open LogicKernel K using (BB)
  open BulkBoundary BB using (Con_bnd)

  module KP = KUP.ForLogicKernel K stepGrade

  mkCodeSocket
    : AgentPorts Sig
    → (LogOSSignature.Iface Sig → Con_bnd)
    → AgentContracts Sig
    → Cat.Choice Task KP.CodeProcess
    → AgentSocket Sig Q Task
  mkCodeSocket ports val∂ C choice =
    record
      { LK     = K
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
      { LK     = K
      ; ports  = ports
      ; val∂   = val∂
      ; C      = C
      ; P      = KP.BoundaryProcess
      ; choice = choice
      }
