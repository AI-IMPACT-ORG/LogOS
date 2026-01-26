{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.Flow where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel
open import LogOS.Kernel.Hom
open import LogOS.Theorems.Meta.Assumptions.Core as A
open import LogOS.Syntax.Prop using (¬_)
open import LogOS.Theorems.Meta.Full as F
open import LogOS.Theorems.Meta.Base using (DeciderC)

-- Stability of the flow body at decode-level (code-side predicate):
-- A code γ is stable if Body∂ (decode γ) ≡ decode γ.

StableP
  : ∀ {ℓ} {Sig : LogOS.Base.Signature.LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q) → Kernel.Code K → Set ℓ
StableP K γ = Kernel.Body∂ K (Kernel.decode K γ) ≡ Kernel.decode K γ

-- Stability is decode-extensional (immediate from equality congruence).

stable-ext
  : ∀ {ℓ} {Sig : LogOS.Base.Signature.LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → A.DecodeExtensional K (StableP K)
stable-ext K γ₁ γ₂ pr st =
  let open Kernel K in
  trans (trans (sym (cong Body∂ pr)) st) pr

-- Transported undecidability (textbook reduction lemma):
-- if the pullback of stability along the canonical fold has no total decider on
-- FreeKernel, then stability has no total decider on K.

noDecider-Stability-transport
  : ∀ {ℓ} {Sig : LogOS.Base.Signature.LogOSSignature ℓ} {Q : QAdapter ℓ}
    (HW : F.WorldH Sig Q)
    (K  : Kernel Sig Q)
  → ¬ (DeciderC {K = F.FreeKernel Sig Q HW}
         (λ γ → StableP K (KernelHom.mapCode (F.foldTo Sig Q HW K) γ)))
  → ¬ (DeciderC {K = K} (StableP K))
noDecider-Stability-transport HW K freeNoDecider =
  F.noDecider-transport HW K (StableP K) freeNoDecider
