{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Socket.FromKernel where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature; module LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Kernel using (Kernel)

import LogOS.Computation.KernelUniversalProcess as KUP
import LogOS.Computation.SchemeCategory as Cat

open import LogOS.Packs.Agents.Socket.Ports using (AgentPorts)
open import LogOS.Packs.Agents.Socket.Contracts using (AgentContracts)
open import LogOS.Packs.Agents.Socket.Core using (AgentSocket)

-- Canonical construction: any `Kernel` yields a socket parameterized by a
-- chosen step grade, exposing code or boundary processes.

module For
  {ℓ ℓTask : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K   : Kernel Sig Q)
  (stepGrade : QAdapter.Scale Q)
  (Task : Set ℓTask)
  where

  open Kernel K using (BB)
  open BulkBoundary BB using (Con_bnd)

  module KP = KUP.ForKernel K stepGrade

  mkCodeSocket
    : AgentPorts Sig
    → (LogOSSignature.Iface Sig → Con_bnd)
    → AgentContracts Sig
    → Cat.Interface Task KP.CodeProcess
    → AgentSocket Sig Q Task
  mkCodeSocket ports val∂ C interface =
    record
      { LK     = K
      ; ports  = ports
      ; val∂   = val∂
      ; C      = C
      ; P      = KP.CodeProcess
      ; interface = interface
      }

  mkBoundarySocket
    : AgentPorts Sig
    → (LogOSSignature.Iface Sig → Con_bnd)
    → AgentContracts Sig
    → Cat.Interface Task KP.BoundaryProcess
    → AgentSocket Sig Q Task
  mkBoundarySocket ports val∂ C interface =
    record
      { LK     = K
      ; ports  = ports
      ; val∂   = val∂
      ; C      = C
      ; P      = KP.BoundaryProcess
      ; interface = interface
      }
