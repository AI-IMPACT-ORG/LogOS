{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.CHL.Core where

-- Curry-Howard-Lambek as a kernel-native reflection:
-- proofs = refinement on code, semantics = decode, and stable truth = closure at Th*.

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop using (_↔_)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con
  using
    ( ConPreorder
    ; BulkBoundary
    ; MonoOn
    ; monoOn-respects≈
    ; _≈CP_
    ; ≡→≈CP
    ; ≈CP-refl
    ; ≈CP-sym
    ; ≈CP-trans
    )
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel
  renaming
    ( Box       to KBox
    ; decode-Box to decode-KBox
    ; box-mono  to kbox-mono
    )
open import LogOS.Kernel.Core as KCore hiding (FlowCode)
import LogOS.Theorems.Code.Core as CodeCore
import LogOS.Theorems.Meta.ObserverCore as ObsCore

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
  refl-equiv {gamma} = ≈CP-refl (KCore.CodePreorder S) gamma

  sym-equiv : ∀ {gamma delta} → Equiv gamma delta → Equiv delta gamma
  sym-equiv {gamma} {delta} eq =
    ≈CP-sym {CP = KCore.CodePreorder S} {c = gamma} {d = delta} eq

  trans-equiv
    : ∀ {gamma delta epsilon}
    → Equiv gamma delta
    → Equiv delta epsilon
    → Equiv gamma epsilon
  trans-equiv {gamma} {delta} {epsilon} eq₁ eq₂ =
    ≈CP-trans {CP = KCore.CodePreorder S} {a = gamma} {b = delta} {c = epsilon} eq₁ eq₂

  refl-refines : ∀ {gamma} → Refines gamma gamma
  refl-refines = ConPreorder.refl (KCore.CodePreorder S)

  cut-refines
    : ∀ {gamma delta epsilon}
    → Refines gamma delta
    → Refines delta epsilon
    → Refines gamma epsilon
  cut-refines = ConPreorder.trans (KCore.CodePreorder S)

  denote : Ty → ConPreorder.Con CP
  denote = Kernel.decode K

  proofs-as-refinement
    : ∀ {gamma delta}
    → Refines gamma delta
      ↔ ConPreorder._⊑_ CP (denote gamma) (denote delta)
  proofs-as-refinement = Prop.intro (λ le → le) (λ le → le)

  encode-code : ConPreorder.Con CP → Ty
  encode-code = Kernel.encode K

  decode-encode : ∀ c → denote (encode-code c) ≡ c
  decode-encode = Kernel.decode∘encode K

  reify-code : Ty → Ty
  reify-code = Kernel.reify K

  reify-equivalence : ∀ gamma → Equiv (reify-code gamma) gamma
  reify-equivalence = CodeCore.reify≈ K

  -- --------------------------------------------------------------------------
  -- Guarded/operator view:
  -- `RawStep` is the kernel’s raw one-step operator (Guard ∘ Body).
  -- `Step` is the canonical “compute then stabilise” step (`Box (Body _)`).
  -- `Box` is the *stable* (closure) modality on decoded constraints:
  --   Box = encode ∘ Flow ∘ decode.
  -- --------------------------------------------------------------------------

  Flow : ConPreorder.Con CP → ConPreorder.Con CP
  Flow = Truth.GuardedCore.GuardedClosure.Flow (Kernel.GTruth K)

  Box : Ty → Ty
  Box = KBox K

  decode-Box
    : ∀ gamma
    → denote (Box gamma)
      ≡ Flow (denote gamma)
  decode-Box = decode-KBox K

  -- Canonical “compute then stabilise” step.
  Step : Ty → Ty
  Step γ = Box (Kernel.Body K γ)

  decode-Step
    : ∀ gamma
    → denote (Step gamma)
      ≡ Flow (Kernel.Body∂ K (denote gamma))
  decode-Step gamma
    rewrite decode-Box (Kernel.Body K gamma)
          | Kernel.body-decode K gamma
    = refl

  -- Legacy/raw step (operational presentation): `FlowCode = Guard ∘ Body`.
  RawStep : Ty → Ty
  RawStep = FlowCode K

  decode-RawStep
    : ∀ gamma
    → denote (RawStep gamma)
      ≡ Flow (Kernel.Body∂ K (denote gamma))
  decode-RawStep = decode-FlowCode K

  decode-RawStep≡decode-Step
    : ∀ γ → denote (RawStep γ) ≡ denote (Step γ)
  decode-RawStep≡decode-Step = decode-FlowCode≡decode-BoxBody K

  eqStep≈ : ∀ γ → _≈CP_ CP (denote (Step γ)) (denote (RawStep γ))
  eqStep≈ γ = ≡→≈CP {CP = CP} (sym (decode-RawStep≡decode-Step γ))

  module StepTransport =
    ObsCore.StepTransport≈ CP denote Step RawStep eqStep≈

  private
    body-mono
      : ∀ {gamma delta}
      → Refines gamma delta
      → Refines (Kernel.Body K gamma) (Kernel.Body K delta)
    body-mono {gamma} {delta} le
      rewrite Kernel.body-decode K gamma
            | Kernel.body-decode K delta
      = Kernel.mono-Body∂ K le

  box-mono : ∀ {gamma delta} → Refines gamma delta → Refines (Box gamma) (Box delta)
  box-mono = kbox-mono K

  box-monoOn : MonoOn (KCore.CodePreorder S) Box
  box-monoOn {gamma} {delta} le = box-mono {gamma = gamma} {delta = delta} le

  box-respects-equiv : ∀ {gamma delta} → Equiv gamma delta → Equiv (Box gamma) (Box delta)
  box-respects-equiv {gamma} {delta} eq =
    monoOn-respects≈ {CP = KCore.CodePreorder S} box-monoOn eq

  step-mono : ∀ {gamma delta} → Refines gamma delta → Refines (Step gamma) (Step delta)
  step-mono le = box-mono (body-mono le)

  step-monoOn : MonoOn (KCore.CodePreorder S) Step
  step-monoOn {gamma} {delta} le = step-mono {gamma = gamma} {delta = delta} le

  step-respects-equiv : ∀ {gamma delta} → Equiv gamma delta → Equiv (Step gamma) (Step delta)
  step-respects-equiv {gamma} {delta} eq =
    monoOn-respects≈ {CP = KCore.CodePreorder S} step-monoOn eq

  rawStep-mono : ∀ {gamma delta} → Refines gamma delta → Refines (RawStep gamma) (RawStep delta)
  rawStep-mono = CodeCore.flowCode-mono K

  rawStep-monoOn : MonoOn (KCore.CodePreorder S) RawStep
  rawStep-monoOn {gamma} {delta} le = rawStep-mono {gamma = gamma} {delta = delta} le

  rawStep-respects-equiv : ∀ {gamma delta} → Equiv gamma delta → Equiv (RawStep gamma) (RawStep delta)
  rawStep-respects-equiv {gamma} {delta} eq =
    monoOn-respects≈ {CP = KCore.CodePreorder S} rawStep-monoOn eq

  -- --------------------------------------------------------------------------
  -- Distinguished fixed point: stable truth as a code-level witness.
  -- --------------------------------------------------------------------------

  truth : Ty
  truth = Kernel.γ* K

  truth-decoded
    : denote truth ≡ Truth.GuardedCore.GuardedClosure.Th* (Kernel.GTruth K)
  truth-decoded = Kernel.decode-γ* K

  truth-fixed
    : Refines truth (Box truth)
      × Refines (Box truth) truth
  truth-fixed
    rewrite decode-Box truth | truth-decoded
    = Truth.GuardedCore.GuardedClosure.Th*-fixed (Kernel.GTruth K)

  truth≤Box : Refines truth (Box truth)
  truth≤Box = fst truth-fixed

  box≤truth : Refines (Box truth) truth
  box≤truth = snd truth-fixed

  truth-step-fixed
    : Refines truth (Step truth)
      × Refines (Step truth) truth
  truth-step-fixed =
    let
      CPCode = KCore.CodePreorder S
      γ≤raw = fst (Kernel.γ*-guard K)
      raw≤γ = snd (Kernel.γ*-guard K)
      raw≤step = fst (flowCode≈BoxBody K truth)
      step≤raw = snd (flowCode≈BoxBody K truth)
    in
    ( ConPreorder.trans CPCode γ≤raw raw≤step
    , ConPreorder.trans CPCode step≤raw raw≤γ
    )

  truth-rawStep-fixed
    : Refines truth (RawStep truth)
      × Refines (RawStep truth) truth
  truth-rawStep-fixed = Kernel.γ*-guard K
