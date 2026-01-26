{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Socket.FromGradedKernel where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature; module LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Kernel.Graded using (GradedKernel; module GradedKernel)
open import LogOS.Kernel.LogicKernel.FromGradedKernel as LKFromG using (asLogicKernel)
import LogOS.Packs.Agents.Socket.FromLogicKernel as FromLK

-- Canonical construction: any `GradedKernel` yields a socket where the shared
-- process exposes *budgeted* computation (via the kernel’s `step-grade`).

module For
  {ℓ ℓTask : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K   : GradedKernel Sig Q)
  (Task : Set ℓTask)
  where
  module Base = FromLK.For (LKFromG.asLogicKernel K) (GradedKernel.step-grade K) Task
  open Base public
