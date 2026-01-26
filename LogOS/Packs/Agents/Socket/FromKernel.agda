{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Socket.FromKernel where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature; module LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Kernel using (Kernel; module Kernel)
open import LogOS.Kernel.LogicKernel.FromKernel as LKFromK using (asLogicKernel)
import LogOS.Packs.Agents.Socket.FromLogicKernel as FromLK

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
  module Base = FromLK.For (LKFromK.asLogicKernel K) (QAdapter.e Q) Task
  open Base public
