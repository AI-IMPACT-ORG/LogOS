{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Examples.HelloSocket where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature; module LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Kernel using (Kernel; module Kernel)

import LogOS.Computation.SchemeCategory as Cat
import LogOS.Kernel.LogicKernel.Endo as LKEndo

open import LogOS.Packs.Agents.Socket.Ports using (AgentPorts)
open import LogOS.Packs.Agents.Socket.Contracts using (AgentContracts)
open import LogOS.Packs.Agents.Socket.Core using (AgentSocket)
import LogOS.Packs.Agents.Socket.FromKernel as FromKernel
import LogOS.Packs.Agents.Safety.Monitor as Monitor

-- A small “smoke test” for the intended user journey:
-- build a socket from an arbitrary kernel, then construct the canonical
-- safety monitor and expose its underlying boundary endomap.

module For
  {ℓ ℓTask : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K   : Kernel Sig Q)
  (Task : Set ℓTask)
  where

  open Kernel K using (BB)
  open BulkBoundary BB using (Con_bnd)
  open LogOSSignature Sig using (Iface)

  module SK = FromKernel.For K Task

  mkSocket
    : AgentPorts Sig
    → (Iface → Con_bnd)
    → AgentContracts Sig
    → Cat.Choice Task SK.KP.CodeProcess
    → AgentSocket Sig Q Task
  mkSocket = SK.mkCodeSocket

  module _
    (ports : AgentPorts Sig)
    (val∂  : Iface → Con_bnd)
    (C     : AgentContracts Sig)
    (choice : Cat.Choice Task SK.KP.CodeProcess)
    where

    socket : AgentSocket Sig Q Task
    socket = mkSocket ports val∂ C choice

    module Mon = Monitor.For socket

    monitor : Mon.Monitor
    monitor = Mon.defaultMonitor

    monitorFn : Con_bnd → Con_bnd
    monitorFn = LKEndo.Endo.fn monitor
