{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.BodyEquivParam where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel
open import LogOS.Kernel.Hom
open import LogOS.Theorems.Meta.Assumptions.Core as A
open import LogOS.Theorems.Meta.Full as F
open import LogOS.Theorems.Meta.Base using (DeciderC)
open import LogOS.Syntax.Prop using (¬_)

-- Body equivalence to a fixed code δ: Body∂ (decode γ) ≡ Body∂ (decode δ)

BodyEqP
  : ∀ {ℓ} {Sig : LogOS.Base.Signature.LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (δ : Kernel.Code K)
    → Kernel.Code K → Set ℓ
BodyEqP K δ γ = Kernel.Body∂ K (Kernel.decode K γ) ≡ Kernel.Body∂ K (Kernel.decode K δ)

-- Decode-extensionality via congruence

bodyeq-ext
  : ∀ {ℓ} {Sig : LogOS.Base.Signature.LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q) (δ : Kernel.Code K)
  → A.DecodeExtensional K (BodyEqP K δ)
bodyeq-ext K δ γ₁ γ₂ pr st =
  trans (sym (cong (Kernel.Body∂ K) pr)) st

-- Transport undecidability for BodyEqP along the canonical fold.

noDecider-BodyEq-transport
  : ∀ {ℓ} {Sig : LogOS.Base.Signature.LogOSSignature ℓ} {Q : QAdapter ℓ}
    (HW : F.WorldH Sig Q)
    (K  : Kernel Sig Q)
    (δ  : Kernel.Code K)
  → ¬ (DeciderC {K = F.FreeKernel Sig Q HW}
         (λ γ → BodyEqP K δ (KernelHom.mapCode (F.foldTo Sig Q HW K) γ)))
  → ¬ (DeciderC {K = K} (BodyEqP K δ))
noDecider-BodyEq-transport HW K δ freeNoDecider =
  F.noDecider-transport HW K (BodyEqP K δ) freeNoDecider
