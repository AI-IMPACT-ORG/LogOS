{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.ConditionalPacks where

-- Shared *structural* packs used by conditional meta theorems.
--
-- This module is intentionally assumption-light:
-- it does not include diagonalisation/self-reference principles and does not
-- introduce global fixed-point axioms. Those live under
-- `LogOS.Theorems.Meta.Assumptions.*`.

open import LogOS.Prelude
open import LogOS.Prelude using (Σ)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel hiding (Box; decode-Box; box-mono)
open import LogOS.Kernel.Eq using (module ForKernel; module ForKernelLike)
open import LogOS.Theorems.Meta.Base using (NonTrivialC)

-- ---------------------------------------------------------------------------
-- Decode-extensionality (predicate/function compatibility with decoded meaning)
-- ---------------------------------------------------------------------------

DecodeExtensional
  : ∀ {ℓ ℓP} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (P : Kernel.Code K → Set ℓP)
  → Set (ℓ ⊔ ℓP)
-- `DecodeExtensional K P` is not an axiom about `decode` (and does not assume any
-- form of function extensionality). It is a *predicate-compatibility* condition:
-- `P` must be insensitive to code representation beyond decoded meaning.
DecodeExtensional K P =
  let open ForKernel K in
  ∀ γ₁ γ₂ → γ₁ ≃K γ₂ → P γ₁ → P γ₂

DecodeExtensional≈
  : ∀ {ℓ ℓP} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (P : Kernel.Code K → Set ℓP)
  → Set (ℓ ⊔ ℓP)
-- Stronger, preorder-safe variant: `P` is insensitive to code representation
-- up to decoded mutual refinement (in the boundary preorder).
DecodeExtensional≈ K P =
  let open ForKernel K in
  ∀ γ₁ γ₂ → γ₁ ≈K γ₂ → P γ₁ → P γ₂

DecodeExtensionalLike
  : ∀ {ℓ ℓP} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : KernelLike Sig Q)
    (P : KernelLike.Code K → Set ℓP)
  → Set (ℓ ⊔ ℓP)
-- `DecodeExtensionalLike K P` is the same predicate-compatibility condition,
-- but only assumes the kernel *shape* (`KernelLike`), not guarded truth.
DecodeExtensionalLike K P =
  let open ForKernelLike K in
  ∀ γ₁ γ₂ → γ₁ ≃K γ₂ → P γ₁ → P γ₂

DecodeExtensionalLike≈
  : ∀ {ℓ ℓP} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : KernelLike Sig Q)
    (P : KernelLike.Code K → Set ℓP)
  → Set (ℓ ⊔ ℓP)
DecodeExtensionalLike≈ K P =
  let open ForKernelLike K in
  ∀ γ₁ γ₂ → γ₁ ≈K γ₂ → P γ₁ → P γ₂

DecodeExtensional≈→DecodeExtensional
  : ∀ {ℓ ℓP} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
    {P : Kernel.Code K → Set ℓP}
  → DecodeExtensional≈ K P
  → DecodeExtensional K P
DecodeExtensional≈→DecodeExtensional {K = K} {P = P} ext≈ γ₁ γ₂ eq =
  let open ForKernel K in
  ext≈ γ₁ γ₂ (≃K→≈K eq)

DecodeExtensionalLike≈→DecodeExtensionalLike
  : ∀ {ℓ ℓP} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : KernelLike Sig Q}
    {P : KernelLike.Code K → Set ℓP}
  → DecodeExtensionalLike≈ K P
  → DecodeExtensionalLike K P
DecodeExtensionalLike≈→DecodeExtensionalLike {K = K} {P = P} ext≈ γ₁ γ₂ eq =
  let open ForKernelLike K in
  ext≈ γ₁ γ₂ (≃K→≈K eq)

DecodeExtensionalFn
  : ∀ {ℓ ℓX} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    {X : Set ℓX}
    (f : Kernel.Code K → X)
  → Set (ℓ ⊔ ℓX)
-- Function-specialised variant: `f` respects decoded meaning.
DecodeExtensionalFn K f =
  let open ForKernel K in
  ∀ γ₁ γ₂ → γ₁ ≃K γ₂ → f γ₁ ≡ f γ₂

DecodeExtensionalFn≈
  : ∀ {ℓ ℓX} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    {X : Set ℓX}
    (f : Kernel.Code K → X)
  → Set (ℓ ⊔ ℓX)
-- Preorder-safe variant: `f` respects decoded mutual refinement.
DecodeExtensionalFn≈ K f =
  let open ForKernel K in
  ∀ γ₁ γ₂ → γ₁ ≈K γ₂ → f γ₁ ≡ f γ₂

DecodeExtensionalFn≈→DecodeExtensionalFn
  : ∀ {ℓ ℓX} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
    {X : Set ℓX}
    {f : Kernel.Code K → X}
  → DecodeExtensionalFn≈ K f
  → DecodeExtensionalFn K f
DecodeExtensionalFn≈→DecodeExtensionalFn {K = K} ext≈ γ₁ γ₂ eq =
  let open ForKernel K in
  ext≈ γ₁ γ₂ (≃K→≈K eq)

DecodeExtensionalLikeFn
  : ∀ {ℓ ℓX} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : KernelLike Sig Q)
    {X : Set ℓX}
    (f : KernelLike.Code K → X)
  → Set (ℓ ⊔ ℓX)
DecodeExtensionalLikeFn K f =
  let open ForKernelLike K in
  ∀ γ₁ γ₂ → γ₁ ≃K γ₂ → f γ₁ ≡ f γ₂

DecodeExtensionalLikeFn≈
  : ∀ {ℓ ℓX} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : KernelLike Sig Q)
    {X : Set ℓX}
    (f : KernelLike.Code K → X)
  → Set (ℓ ⊔ ℓX)
DecodeExtensionalLikeFn≈ K f =
  let open ForKernelLike K in
  ∀ γ₁ γ₂ → γ₁ ≈K γ₂ → f γ₁ ≡ f γ₂

DecodeExtensionalLikeFn≈→DecodeExtensionalLikeFn
  : ∀ {ℓ ℓX} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : KernelLike Sig Q}
    {X : Set ℓX}
    {f : KernelLike.Code K → X}
  → DecodeExtensionalLikeFn≈ K f
  → DecodeExtensionalLikeFn K f
DecodeExtensionalLikeFn≈→DecodeExtensionalLikeFn {K = K} ext≈ γ₁ γ₂ eq =
  let open ForKernelLike K in
  ext≈ γ₁ γ₂ (≃K→≈K eq)

-- ---------------------------------------------------------------------------
-- Kernel-independent provability scaffolding (reused by Löb/Gödel core).
-- ---------------------------------------------------------------------------

record ProvabilityOpsC {ℓCode : Level} (Code : Set ℓCode) : Set (lsuc ℓCode) where
  field
    Imp : Code → Code → Code
    Box : Code → Code

record ImpRulesC {ℓCode ℓPr : Level}
                 {Code : Set ℓCode}
                 (⊢    : Code → Set ℓPr)
                 (Op   : ProvabilityOpsC Code)
                 : Set (lsuc (ℓCode ⊔ ℓPr)) where
  open ProvabilityOpsC Op
  field
    mp   : ∀ {φ ψ} → ⊢ (Imp φ ψ) → ⊢ φ → ⊢ ψ
    impI : ∀ {φ ψ} → (⊢ φ → ⊢ ψ) → ⊢ (Imp φ ψ)

record HBLClassicC {ℓCode ℓPr : Level}
                   {Code : Set ℓCode}
                   (⊢    : Code → Set ℓPr)
                   (Op   : ProvabilityOpsC Code)
                   : Set (lsuc (ℓCode ⊔ ℓPr)) where
  open ProvabilityOpsC Op
  field
    Necessitation : ∀ φ → ⊢ φ → ⊢ (Box φ)
    Kdist         : ∀ φ ψ → ⊢ (Box (Imp φ ψ)) → (⊢ (Box φ) → ⊢ (Box ψ))
    Four          : ∀ φ → ⊢ (Box φ) → ⊢ (Box (Box φ))

record Provability {ℓ}
                   {Sig : LogOSSignature ℓ}
                   {Q : QAdapter ℓ}
                   (K : Kernel Sig Q)
                   : Set (lsuc ℓ) where
  field
    Prov    : Kernel.Code K → Set ℓ
    ext     : DecodeExtensional K Prov
    nontriv : NonTrivialC {K = K} Prov

record ProvabilityOps {ℓ}
                      {Sig : LogOSSignature ℓ}
                      {Q : QAdapter ℓ}
                      (K : Kernel Sig Q)
                      : Set (lsuc ℓ) where
  open Kernel K
  field
    Imp : Code → Code → Code
    Box : Code → Code

toOpsC
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
  → ProvabilityOps K
  → ProvabilityOpsC (Kernel.Code K)
toOpsC Op = record
  { Imp = ProvabilityOps.Imp Op
  ; Box = ProvabilityOps.Box Op
  }

-- Minimal implicational fragment over the model-provided `Imp` constructor.
-- We keep this separate so metatheorems can precisely state when they need
-- “plain” propositional reasoning in addition to provability-side axioms.

record ImpRules {ℓ}
                {Sig : LogOSSignature ℓ}
                {Q : QAdapter ℓ}
                (K  : Kernel Sig Q)
                (Pr : Provability K)
                (Op : ProvabilityOps K)
                : Set (lsuc ℓ) where
  open Provability Pr renaming (Prov to ⊢)
  open ProvabilityOps Op
  field
    mp   : ∀ {φ ψ} → ⊢ (Imp φ ψ) → ⊢ φ → ⊢ ψ
    impI : ∀ {φ ψ} → (⊢ φ → ⊢ ψ) → ⊢ (Imp φ ψ)

toImpRulesC
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K  : Kernel Sig Q}
    {Pr : Provability K}
    {Op : ProvabilityOps K}
  → ImpRules K Pr Op
  → ImpRulesC (Provability.Prov Pr) (toOpsC Op)
toImpRulesC Ir = record
  { mp   = ImpRules.mp Ir
  ; impI = ImpRules.impI Ir
  }

-- HBL (classic):
-- 1) Necessitation: if ⊢ φ then ⊢ Box φ
-- 2) Distribution (K): ⊢ Box(φ → ψ) → (Box φ → Box ψ)
-- 3) 4-axiom: ⊢ Box φ → Box Box φ

record HBLClassic {ℓ}
                  {Sig : LogOSSignature ℓ}
                  {Q   : QAdapter ℓ}
                  (K  : Kernel Sig Q)
                  (Pr : Provability K)
                  (Op : ProvabilityOps K)
                  : Set (lsuc ℓ) where
  open Provability Pr renaming (Prov to ⊢)
  open ProvabilityOps Op
  field
    Necessitation : ∀ φ → ⊢ φ → ⊢ (Box φ)
    Kdist         : ∀ φ ψ → ⊢ (Box (Imp φ ψ)) → (⊢ (Box φ) → ⊢ (Box ψ))
    Four          : ∀ φ → ⊢ (Box φ) → ⊢ (Box (Box φ))

toHBLClassicC
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K  : Kernel Sig Q}
    {Pr : Provability K}
    {Op : ProvabilityOps K}
  → HBLClassic K Pr Op
  → HBLClassicC (Provability.Prov Pr) (toOpsC Op)
toHBLClassicC Hb = record
  { Necessitation = HBLClassic.Necessitation Hb
  ; Kdist         = HBLClassic.Kdist Hb
  ; Four          = HBLClassic.Four Hb
  }
