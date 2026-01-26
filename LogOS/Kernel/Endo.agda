{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Endo where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel
open import LogOS.Kernel.LogicKernel.FromKernel as LKFrom
open import LogOS.Kernel.EndoCore as EndoCore

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} where
  private
    ops : EndoCore.Ops Sig Q
    ops =
      record
        { Obj          = Kernel Sig Q
        ; asLogicKernel = LKFrom.asLogicKernel
        }

  open EndoCore.WithOps {Sig = Sig} {Q = Q} ops public

-- All endomap DSL definitions are provided by `EndoCore` for kernels.
