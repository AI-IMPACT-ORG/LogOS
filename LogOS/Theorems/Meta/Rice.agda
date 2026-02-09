{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.Rice where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

open import LogOS.Theorems.Meta.Base using (DeciderC)
open import LogOS.Theorems.Meta.Full as F
open import LogOS.Kernel.Hom

-- Transport shape (textbook reduction lemma):
-- if the pullback of P along the canonical fold has no total decider on the
-- canonical FreeKernel, then P has no total decider on K.

noDecider-Rice
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (HW : F.WorldH Sig Q)
    (K  : Kernel Sig Q)
    (P  : Kernel.Code K → Set ℓ)
  → ¬ (DeciderC {K = F.FreeKernel Sig Q HW}
         (λ γ → P (KernelHom.mapCode (F.foldTo Sig Q HW K) γ)))
  → ¬ (DeciderC {K = K} P)
noDecider-Rice HW K P freeNoDecider =
  F.noDecider-transport HW K P freeNoDecider
