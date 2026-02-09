{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.CHL.Graded where

-- Graded view: use saturation flow (cost → ∞) as the canonical modality on code.
--
-- This avoids the `StepIsSat` assumption: the CHL `Box` operator is defined
-- directly as `encode ∘ Flow sat ∘ decode`, while the kernel’s operational
-- raw one-step operator remains available separately as `RawStep = FlowCode`.

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
    ; ≈CP⇒
    ; ≈CP⇐
    ; ≡→≈CP
    ; ≈CP-refl
    ; ≈CP-sym
    ; ≈CP-trans
    )

open import LogOS.Kernel.Shape as KCore hiding (FlowCode)
open import LogOS.Kernel.Graded
  renaming
    ( Box       to KBox
    ; decode-Box to decode-KBox
    ; box-mono  to kbox-mono
    )

import LogOS.Minimal.Con.Rewrite as ConRewrite
import LogOS.Theorems.Meta.ObserverCore as ObsCore

module For
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  where

  private
    S  = GradedKernel.shape K
    CP = BulkBoundary.bnd (GradedKernel.BB K)
    module R = ConRewrite.For CP

  -- --------------------------------------------------------------------------
  -- Core CHL surface: types/propositions are kernel code.
  -- --------------------------------------------------------------------------

  Ty : Set ℓ
  Ty = GradedKernel.Code K

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
  denote = GradedKernel.decode K

  proofs-as-refinement
    : ∀ {gamma delta}
    → Refines gamma delta
      ↔ ConPreorder._⊑_ CP (denote gamma) (denote delta)
  proofs-as-refinement = Prop.intro (λ le → le) (λ le → le)

  encode-code : ConPreorder.Con CP → Ty
  encode-code = GradedKernel.encode K

  decode-encode : ∀ c → denote (encode-code c) ≡ c
  decode-encode = GradedKernel.decode∘encode K

  reify-code : Ty → Ty
  reify-code = GradedKernel.reify K

  reify-equivalence : ∀ gamma → Equiv (reify-code gamma) gamma
  reify-equivalence gamma =
    let
      eq = GradedKernel.reify-decode K gamma
      reflCP = ConPreorder.refl CP {c = denote gamma}
    in
    ( R.substL (sym eq) reflCP
    , R.substR (sym eq) reflCP
    )

  -- --------------------------------------------------------------------------
  -- Guarded/operator view:
  -- `RawStep` is the kernel’s raw one-step operator (Guard ∘ Body) at step-grade.
  -- `Step` is the canonical “compute then stabilise” step (`BoxAt step (Body _)`).
  -- `Box` is the *stable* (saturation) modality on decoded constraints:
  --   Box = encode ∘ Flow sat ∘ decode.
  -- --------------------------------------------------------------------------

  -- Canonical “compute then stabilise” step at the step grade.
  Step : Ty → Ty
  Step γ = BoxAt K (GradedKernel.step-grade K) (GradedKernel.Body K γ)

  decode-Step
    : ∀ gamma
    → denote (Step gamma)
      ≡ GradedClosure.Flow (GradedKernel.GTruth K) (GradedKernel.step-grade K)
          (GradedKernel.Body∂ K (denote gamma))
  decode-Step gamma
    rewrite decode-BoxAt K (GradedKernel.step-grade K) (GradedKernel.Body K gamma)
          | GradedKernel.body-decode K gamma
    = refl

  -- Raw operational step: `FlowCode = Guard ∘ Body`.
  RawStep : Ty → Ty
  RawStep = FlowCode K

  decode-RawStep
    : ∀ gamma
    → denote (RawStep gamma)
      ≡ GradedClosure.Flow (GradedKernel.GTruth K) (GradedKernel.step-grade K)
          (GradedKernel.Body∂ K (denote gamma))
  decode-RawStep = decode-FlowCode K

  decode-RawStep≡decode-Step
    : ∀ γ → denote (RawStep γ) ≡ denote (Step γ)
  decode-RawStep≡decode-Step = decode-FlowCode≡decode-BoxAt-step-body K

  eqStep≈ : ∀ γ → _≈CP_ CP (denote (Step γ)) (denote (RawStep γ))
  eqStep≈ γ = ≡→≈CP {CP = CP} (sym (decode-RawStep≡decode-Step γ))

  module StepTransport =
    ObsCore.StepTransport≈ CP denote Step RawStep eqStep≈

  Box : Ty → Ty
  Box = KBox K

  decode-Box
    : ∀ gamma
    → denote (Box gamma)
      ≡ GradedClosure.Flow (GradedKernel.GTruth K) (GradedClosure.sat (GradedKernel.GTruth K))
          (denote gamma)
  decode-Box = decode-KBox K

  box-mono : ∀ {gamma delta} → Refines gamma delta → Refines (Box gamma) (Box delta)
  box-mono = kbox-mono K

  box-monoOn : MonoOn (KCore.CodePreorder S) Box
  box-monoOn {gamma} {delta} le = box-mono {gamma = gamma} {delta = delta} le

  box-respects-equiv : ∀ {gamma delta} → Equiv gamma delta → Equiv (Box gamma) (Box delta)
  box-respects-equiv {gamma} {delta} eq =
    monoOn-respects≈ {CP = KCore.CodePreorder S} box-monoOn eq

  -- --------------------------------------------------------------------------
  -- Distinguished fixed-point witness: stable truth as a code-level witness.
  -- --------------------------------------------------------------------------

  truth : Ty
  truth = GradedKernel.γ* K

  truth-decoded
    : denote truth ≡ GradedClosure.Th* (GradedKernel.GTruth K)
  truth-decoded = GradedKernel.decode-γ* K

  truth-fixed
    : Refines truth (Box truth)
      × Refines (Box truth) truth
  truth-fixed
    rewrite decode-Box truth | truth-decoded
    = GradedClosure.Th*-fixed (GradedKernel.GTruth K)

  truth≤Box : Refines truth (Box truth)
  truth≤Box = ≈CP⇒ {CP = KCore.CodePreorder S} truth-fixed

  box≤truth : Refines (Box truth) truth
  box≤truth = ≈CP⇐ {CP = KCore.CodePreorder S} truth-fixed

  truth-step-fixed
    : Refines truth (Step truth)
      × Refines (Step truth) truth
  truth-step-fixed =
    let
      CPCode = KCore.CodePreorder S
      γ≤raw = GradedKernel.γ*-guard⇒ K
      raw≤γ = GradedKernel.γ*-guard⇐ K
      raw≤step = ≈CP⇒ {CP = CPCode} (flowCode≈BoxAt-step-body K truth)
      step≤raw = ≈CP⇐ {CP = CPCode} (flowCode≈BoxAt-step-body K truth)
    in
    ( ConPreorder.trans CPCode γ≤raw raw≤step
    , ConPreorder.trans CPCode step≤raw raw≤γ
    )

  truth-rawStep-fixed
    : Refines truth (RawStep truth)
      × Refines (RawStep truth) truth
  truth-rawStep-fixed = GradedKernel.γ*-guard K
