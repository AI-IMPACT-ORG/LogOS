{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Code.Graded where

-- Decode-level equivalences around reify, body, and FlowCode (graded kernel).
-- These expose equalities from the GradedKernel fields and provide
-- guard naturality under graded kernel homs.

open import LogOS.Prelude

open import LogOS.Kernel.Graded
open import LogOS.Kernel.Core as KCore
open import LogOS.Kernel.Graded.Hom
open import LogOS.Minimal.Con
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter

-- Guard naturality at decode-level (lax): under a graded kernel homomorphism with
-- Flow preservation and step-grade alignment, decoding mapCode (Guard γ) lies
-- below F₂ at the target step grade.

guard-naturality-decode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K₁ K₂ : GradedKernel Sig Q)
    (h  : GradedKernelHom K₁ K₂)
    (ht : GradedKernelHomFlow K₁ K₂ h)
    (γ  : GradedKernel.Code K₁)
  → ConPoset._⊑_ (BulkBoundary.bnd (GradedKernel.BB K₂))
                 (GradedKernel.decode K₂ (GradedKernelHom.mapCode h (GradedKernel.Guard K₁ γ)))
                 (GradedClosure.Flow (GradedKernel.GTruth K₂) (GradedKernel.step-grade K₂)
                   (GradedKernel.decode K₂ (GradedKernelHom.mapCode h γ)))
guard-naturality-decode K₁ K₂ h ht γ =
  map-guard-decode≤ {K₁ = K₁} {K₂ = K₂} {h = h} ht γ

-- Packaged guard naturality (decode-level).

record GuardHom {ℓ}
                {Sig : LogOSSignature ℓ}
                {Q : QAdapter ℓ}
                (K₁ K₂ : GradedKernel Sig Q)
                (h  : GradedKernelHom K₁ K₂)
                (ht : GradedKernelHomFlow K₁ K₂ h)
                : Set (lsuc ℓ) where
  field
    natural-decode : ∀ γ → ConPoset._⊑_ (BulkBoundary.bnd (GradedKernel.BB K₂))
                               (GradedKernel.decode K₂ (GradedKernelHom.mapCode h (GradedKernel.Guard K₁ γ)))
                               (GradedClosure.Flow (GradedKernel.GTruth K₂) (GradedKernel.step-grade K₂)
                                 (GradedKernel.decode K₂ (GradedKernelHom.mapCode h γ)))

guardHom-from
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K₁ K₂ : GradedKernel Sig Q)
    (h  : GradedKernelHom K₁ K₂)
    (ht : GradedKernelHomFlow K₁ K₂ h)
  → GuardHom K₁ K₂ h ht
guardHom-from K₁ K₂ h ht = record
  { natural-decode = guard-naturality-decode K₁ K₂ h ht }

-- Reify and body decode-level equalities (expose GradedKernel fields as theorems).

reify-decode-eq
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (γ : GradedKernel.Code K)
  → (GradedKernel.decode K (GradedKernel.reify K γ)) ≡ (GradedKernel.decode K γ)
reify-decode-eq K γ = GradedKernel.reify-decode K γ

body-decode-eq
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (γ : GradedKernel.Code K)
  → (GradedKernel.decode K (GradedKernel.Body K γ))
    ≡ (GradedKernel.Body∂ K (GradedKernel.decode K γ))
body-decode-eq K γ = GradedKernel.body-decode K γ

-- Reify compatibility with Guard/Body (up to decode-level equality).
-- This is intentionally weaker than any extensionality/canonicity condition on `Code`.

reify-guard-decode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (γ : GradedKernel.Code K)
  → GradedKernel.decode K (GradedKernel.reify K (GradedKernel.Guard K γ))
    ≡ GradedKernel.decode K (GradedKernel.Guard K (GradedKernel.reify K γ))
reify-guard-decode K γ =
  let open GradedKernel K
      F = GradedClosure.Flow GTruth step-grade
  in
  trans (GradedKernel.reify-decode K (GradedKernel.Guard K γ))
    (trans (GradedKernel.guard-decode K γ)
      (trans (cong F (sym (GradedKernel.reify-decode K γ)))
        (sym (GradedKernel.guard-decode K (GradedKernel.reify K γ)))))

reify-body-decode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (γ : GradedKernel.Code K)
  → GradedKernel.decode K (GradedKernel.reify K (GradedKernel.Body K γ))
    ≡ GradedKernel.decode K (GradedKernel.Body K (GradedKernel.reify K γ))
reify-body-decode K γ =
  trans (GradedKernel.reify-decode K (GradedKernel.Body K γ))
    (trans (GradedKernel.body-decode K γ)
      (trans (cong (GradedKernel.Body∂ K) (sym (GradedKernel.reify-decode K γ)))
        (sym (GradedKernel.body-decode K (GradedKernel.reify K γ)))))

-- Factorization at decode-level: prefer Guard ∘ Body on the code layer.

decode-FlowCode-eq
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (γ : GradedKernel.Code K)
  → GradedKernel.decode K (FlowCode K γ)
    ≡ GradedClosure.Flow (GradedKernel.GTruth K) (GradedKernel.step-grade K)
        (GradedKernel.Body∂ K (GradedKernel.decode K γ))
decode-FlowCode-eq K γ = decode-FlowCode K γ

-- ============================================================================
-- Trust helpers: make γ* fixed-point and FlowCode monotonicity explicit.
-- ============================================================================

γ*-decode≤stepBody
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → ConPoset._⊑_ (BulkBoundary.bnd (GradedKernel.BB K))
      (GradedKernel.decode K (GradedKernel.γ* K))
      (GradedClosure.Flow (GradedKernel.GTruth K) (GradedKernel.step-grade K)
        (GradedKernel.Body∂ K (GradedKernel.decode K (GradedKernel.γ* K))))
γ*-decode≤stepBody K =
  let
    CP = BulkBoundary.bnd (GradedKernel.BB K)
    le = fst (GradedKernel.γ*-guard K)
    eq = decode-FlowCode-eq K (GradedKernel.γ* K)
  in
  subst
    (λ x → ConPoset._⊑_ CP (GradedKernel.decode K (GradedKernel.γ* K)) x)
    eq
    le

stepBody≤γ*-decode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → ConPoset._⊑_ (BulkBoundary.bnd (GradedKernel.BB K))
      (GradedClosure.Flow (GradedKernel.GTruth K) (GradedKernel.step-grade K)
        (GradedKernel.Body∂ K (GradedKernel.decode K (GradedKernel.γ* K))))
      (GradedKernel.decode K (GradedKernel.γ* K))
stepBody≤γ*-decode K =
  let
    CP = BulkBoundary.bnd (GradedKernel.BB K)
    le = snd (GradedKernel.γ*-guard K)
    eq = decode-FlowCode-eq K (GradedKernel.γ* K)
  in
  subst
    (λ x → ConPoset._⊑_ CP x (GradedKernel.decode K (GradedKernel.γ* K)))
    eq
    le

decode-FlowCode-γ*-eq
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → BulkBoundaryPO (GradedKernel.BB K)
  → GradedKernel.decode K (FlowCode K (GradedKernel.γ* K)) ≡ GradedKernel.decode K (GradedKernel.γ* K)
decode-FlowCode-γ*-eq K po =
  let
    open GradedKernel K
    open BulkBoundaryPO po using (po-bnd)
    open PartialOrder po-bnd using (antisym)
    le₁ = fst (GradedKernel.γ*-guard K)
    le₂ = snd (GradedKernel.γ*-guard K)
  in antisym le₂ le₁

decode-FlowCode-mono
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → KCore.BodyMonotoneShape (GradedKernel.shape K)
  → ∀ {γ δ}
  → ConPoset._⊑_ (BulkBoundary.bnd (GradedKernel.BB K)) (GradedKernel.decode K γ) (GradedKernel.decode K δ)
  → ConPoset._⊑_ (BulkBoundary.bnd (GradedKernel.BB K))
      (GradedKernel.decode K (FlowCode K γ))
      (GradedKernel.decode K (FlowCode K δ))
decode-FlowCode-mono K bm {γ} {δ} le =
  let
    open GradedKernel K
    CP = BulkBoundary.bnd (GradedKernel.BB K)
    F  = GradedClosure.Flow GTruth step-grade
    bodyLe = KCore.BodyMonotoneShape.mono-Body∂ bm le
    flowLe : ConPoset._⊑_ CP (F (GradedKernel.Body∂ K (GradedKernel.decode K γ))) (F (GradedKernel.Body∂ K (GradedKernel.decode K δ)))
    flowLe = GradedClosure.mono GTruth bodyLe
    eqγ = decode-FlowCode-eq K γ
    eqδ = decode-FlowCode-eq K δ
    flowLe' : ConPoset._⊑_ CP (F (GradedKernel.Body∂ K (GradedKernel.decode K γ))) (GradedKernel.decode K (FlowCode K δ))
    flowLe' = subst (λ x → ConPoset._⊑_ CP (F (GradedKernel.Body∂ K (GradedKernel.decode K γ))) x) (sym eqδ) flowLe
  in subst (λ x → ConPoset._⊑_ CP x (GradedKernel.decode K (FlowCode K δ))) (sym eqγ) flowLe'

-- Textbook alias: monotonicity of the operational step (FlowCode), under BodyMonotone.

flowcode-mono-decode = decode-FlowCode-mono
