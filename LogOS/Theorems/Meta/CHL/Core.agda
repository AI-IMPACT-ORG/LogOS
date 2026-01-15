{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.CHL.Core where

-- Curry-Howard-Lambek as a kernel-native reflection:
-- proofs = refinement on code, semantics = decode, and guarded stability = FlowCode.

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop using (_↔_)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con
  using
    ( ConPoset
    ; BulkBoundary
    ; MonoOn
    ; monoOn-respects≈
    ; _≈CP_
    ; ≈CP-refl
    ; ≈CP-sym
    ; ≈CP-trans
    )
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel
open import LogOS.Kernel.Core as KCore hiding (FlowCode)
import LogOS.Theorems.Code.Core as CodeCore

module For
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  where

  private
    S  = Kernel.shape K
    CP = BulkBoundary.bnd (Kernel.BB K)

  -- --------------------------------------------------------------------------
  -- Core CHL surface: types/propositions are kernel code.
  -- --------------------------------------------------------------------------

  Ty : Set ℓ
  Ty = Kernel.Code K

  Refines : Ty → Ty → Set ℓ
  Refines = KCore.Code≤ S

  Equiv : Ty → Ty → Set ℓ
  Equiv = KCore.Code≈ S

  refl-equiv : ∀ {gamma} → Equiv gamma gamma
  refl-equiv {gamma} = ≈CP-refl (KCore.CodePoset S) gamma

  sym-equiv : ∀ {gamma delta} → Equiv gamma delta → Equiv delta gamma
  sym-equiv {gamma} {delta} eq =
    ≈CP-sym {CP = KCore.CodePoset S} {c = gamma} {d = delta} eq

  trans-equiv
    : ∀ {gamma delta epsilon}
    → Equiv gamma delta
    → Equiv delta epsilon
    → Equiv gamma epsilon
  trans-equiv {gamma} {delta} {epsilon} eq₁ eq₂ =
    ≈CP-trans {CP = KCore.CodePoset S} {a = gamma} {b = delta} {c = epsilon} eq₁ eq₂

  refl-refines : ∀ {gamma} → Refines gamma gamma
  refl-refines = ConPoset.refl (KCore.CodePoset S)

  cut-refines
    : ∀ {gamma delta epsilon}
    → Refines gamma delta
    → Refines delta epsilon
    → Refines gamma epsilon
  cut-refines = ConPoset.trans (KCore.CodePoset S)

  denote : Ty → ConPoset.Con CP
  denote = Kernel.decode K

  proofs-as-refinement
    : ∀ {gamma delta}
    → Refines gamma delta
      ↔ ConPoset._⊑_ CP (denote gamma) (denote delta)
  proofs-as-refinement = Prop.intro (λ le → le) (λ le → le)

  encode-code : ConPoset.Con CP → Ty
  encode-code = Kernel.encode K

  decode-encode : ∀ c → denote (encode-code c) ≡ c
  decode-encode = Kernel.decode∘encode K

  reify-code : Ty → Ty
  reify-code = Kernel.reify K

  reify-equivalence : ∀ gamma → Equiv (reify-code gamma) gamma
  reify-equivalence = CodeCore.reify≈ K

  -- --------------------------------------------------------------------------
  -- Guarded/operator view: FlowCode is the “modal” operator on code.
  -- --------------------------------------------------------------------------

  Box : Ty → Ty
  Box = FlowCode K

  Flow : ConPoset.Con CP → ConPoset.Con CP
  Flow = Truth.GuardedCore.GuardedClosure.Flow (Kernel.GTruth K)

  decode-Box
    : ∀ gamma
    → denote (Box gamma)
      ≡ Flow (Kernel.Body∂ K (denote gamma))
  decode-Box = decode-FlowCode K

  box-mono : ∀ {gamma delta} → Refines gamma delta → Refines (Box gamma) (Box delta)
  box-mono = CodeCore.flowCode-mono K

  box-monoOn : MonoOn (KCore.CodePoset S) Box
  box-monoOn {gamma} {delta} le = box-mono {gamma = gamma} {delta = delta} le

  box-respects-equiv : ∀ {gamma delta} → Equiv gamma delta → Equiv (Box gamma) (Box delta)
  box-respects-equiv {gamma} {delta} eq =
    monoOn-respects≈ {CP = KCore.CodePoset S} box-monoOn eq

  -- --------------------------------------------------------------------------
  -- Distinguished fixed point: guarded truth as a code-level witness.
  -- --------------------------------------------------------------------------

  truth : Ty
  truth = Kernel.γ* K

  truth-fixed
    : Refines truth (Box truth)
      × Refines (Box truth) truth
  truth-fixed = Kernel.γ*-guard K

  truth≤Box : Refines truth (Box truth)
  truth≤Box = fst truth-fixed

  box≤truth : Refines (Box truth) truth
  box≤truth = snd truth-fixed

  truth-decoded
    : denote truth ≡ Truth.GuardedCore.GuardedClosure.Th* (Kernel.GTruth K)
  truth-decoded = Kernel.decode-γ* K
