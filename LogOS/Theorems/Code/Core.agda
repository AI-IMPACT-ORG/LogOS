{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Code.Core where

-- Decode-level equivalences around reify, body, and FlowCode
-- factorization. These expose equalities from the Kernel fields and provide
-- guard naturality under Kernel homs.

open import LogOS.Prelude

open import LogOS.Kernel
open import LogOS.Kernel.Shape as KCore hiding (FlowCode)
open import LogOS.Kernel.Endo
open import LogOS.Kernel.Hom
open import LogOS.Minimal.Con
import LogOS.Minimal.Con.Rewrite as ConRewrite
open import LogOS.Minimal.Truth as Truth
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.ConAlg
open import LogOS.Kernel.Eq using (module ForKernel)

-- Guard naturality at decode-level (lax): under a Kernel homomorphism with
-- Flow preservation, decoding mapCode (Guard γ) lies below F₂ (decoding mapCode γ).

guard-naturality-decode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K₁ K₂ : Kernel Sig Q)
    (h  : KernelHom K₁ K₂)
    (ht : KernelHomFlow K₁ K₂ h)
    (step≡sat₁ : GTier.step (Kernel.G K₁) ≡ GTier.sat (Kernel.G K₁))
    (γ  : Kernel.Code K₁)
  → ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K₂))
                 (Kernel.decode K₂ (KernelHom.mapCode h (Kernel.Guard K₁ γ)))
                 (Endo.fn (Flow-Endo K₂) (Kernel.decode K₂ (KernelHom.mapCode h γ)))
guard-naturality-decode {Sig = Sig} {Q = Q} K₁ K₂ h ht step≡sat₁ γ =
  let
    module GT0 = Truth.GuardedTruth Sig Q

    open KernelHom h
    open KernelHomFlow ht
    open GT0.FlowHom flow-hom using (preserves-F)

    CP₂ = BulkBoundary.bnd (Kernel.BB K₂)
    map∂ = ConAlgHom≡.map∂ (KernelHom.con-hom h)

    F₁ = Endo.fn (Flow-Endo K₁)
    F₂ = Endo.fn (Flow-Endo K₂)

    guard-as-sat
      : Kernel.decode K₁ (Kernel.Guard K₁ γ) ≡ F₁ (Kernel.decode K₁ γ)
    guard-as-sat =
      trans
        (Kernel.guard-decode K₁ γ)
        (cong (λ g → GTier.Flow (Kernel.G K₁) g (Kernel.decode K₁ γ)) step≡sat₁)

    eq₁ : Kernel.decode K₂ (KernelHom.mapCode h (Kernel.Guard K₁ γ))
          ≡ map∂ (Kernel.decode K₁ (Kernel.Guard K₁ γ))
    eq₁ = KernelHom.map-decode h (Kernel.Guard K₁ γ)

    eq₂ : Kernel.decode K₂ (KernelHom.mapCode h γ)
          ≡ map∂ (Kernel.decode K₁ γ)
    eq₂ = KernelHom.map-decode h γ

    step : ConPreorder._⊑_ CP₂
             (map∂ (F₁ (Kernel.decode K₁ γ)))
             (F₂ (Kernel.decode K₂ (KernelHom.mapCode h γ)))
    step =
      subst
        (λ y →
          ConPreorder._⊑_ CP₂
            (map∂ (F₁ (Kernel.decode K₁ γ)))
            (F₂ y))
        (sym eq₂)
        (preserves-F (Kernel.decode K₁ γ))
  in
  subst
    (λ x →
      ConPreorder._⊑_ CP₂ x
        (F₂ (Kernel.decode K₂ (KernelHom.mapCode h γ))))
    (sym (trans eq₁ (cong map∂ guard-as-sat)))
    step

-- Packaged guard naturality (decode-level)

record GuardHom {ℓ}
                {Sig : LogOSSignature ℓ}
                {Q : QAdapter ℓ}
                (K₁ K₂ : Kernel Sig Q)
                (h  : KernelHom K₁ K₂)
                (ht : KernelHomFlow K₁ K₂ h)
                (step≡sat₁ : GTier.step (Kernel.G K₁) ≡ GTier.sat (Kernel.G K₁))
                : Set (lsuc ℓ) where
  field
    natural-decode : ∀ γ → ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K₂))
                               (Kernel.decode K₂ (KernelHom.mapCode h (Kernel.Guard K₁ γ)))
                               (Endo.fn (Flow-Endo K₂)
                                 (Kernel.decode K₂ (KernelHom.mapCode h γ)))

guardHom-from
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K₁ K₂ : Kernel Sig Q)
    (h  : KernelHom K₁ K₂)
    (ht : KernelHomFlow K₁ K₂ h)
    (step≡sat₁ : GTier.step (Kernel.G K₁) ≡ GTier.sat (Kernel.G K₁))
  → GuardHom K₁ K₂ h ht step≡sat₁
guardHom-from K₁ K₂ h ht step≡sat₁ = record
  { natural-decode = guard-naturality-decode K₁ K₂ h ht step≡sat₁ }

-- Box naturality at decode-level (lax): under a Kernel homomorphism with
-- Flow preservation, decoding mapCode (Box₁ γ) lies below decoding Box₂ (mapCode γ).

box-naturality-decode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K₁ K₂ : Kernel Sig Q)
    (h  : KernelHom K₁ K₂)
    (ht : KernelHomFlow K₁ K₂ h)
    (γ  : Kernel.Code K₁)
  → ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K₂))
      (Kernel.decode K₂ (KernelHom.mapCode h (Box K₁ γ)))
      (Kernel.decode K₂ (Box K₂ (KernelHom.mapCode h γ)))
box-naturality-decode {Sig = Sig} {Q = Q} K₁ K₂ h ht γ =
  map-box-decode≤ {Sig = Sig} {Q = Q} {K₁ = K₁} {K₂ = K₂} {h = h} ht γ

record BoxHom {ℓ}
              {Sig : LogOSSignature ℓ}
              {Q : QAdapter ℓ}
              (K₁ K₂ : Kernel Sig Q)
              (h  : KernelHom K₁ K₂)
              (ht : KernelHomFlow K₁ K₂ h)
              : Set (lsuc ℓ) where
  field
    natural-decode
      : ∀ γ → ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K₂))
                 (Kernel.decode K₂ (KernelHom.mapCode h (Box K₁ γ)))
                 (Kernel.decode K₂ (Box K₂ (KernelHom.mapCode h γ)))

boxHom-from
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K₁ K₂ : Kernel Sig Q)
    (h  : KernelHom K₁ K₂)
    (ht : KernelHomFlow K₁ K₂ h)
  → BoxHom K₁ K₂ h ht
boxHom-from K₁ K₂ h ht =
  record
    { natural-decode = box-naturality-decode K₁ K₂ h ht
    }

-- Reify and body decode-level equalities (expose Kernel fields as theorems)

reify-decode-eq
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (γ : Kernel.Code K)
  → (Kernel.decode K (Kernel.reify K γ)) ≡ (Kernel.decode K γ)
reify-decode-eq K γ = Kernel.reify-decode K γ

body-decode-eq
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (γ : Kernel.Code K)
  → (Kernel.decode K (Kernel.Body K γ)) ≡ (Kernel.Body∂ K (Kernel.decode K γ))
body-decode-eq K γ = Kernel.body-decode K γ

-- Reify compatibility with Guard/Body (up to strict decode equality (`≡`)).
-- This is intentionally weaker than any extensionality/canonicity condition on `Code`.

reify-guard-decode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (γ : Kernel.Code K)
  → Kernel.decode K (Kernel.reify K (Kernel.Guard K γ))
    ≡ Kernel.decode K (Kernel.Guard K (Kernel.reify K γ))
reify-guard-decode {Sig = Sig} {Q = Q} K γ =
  let
    F = GTier.Flow (Kernel.G K) (GTier.step (Kernel.G K))
  in
  trans (Kernel.reify-decode K (Kernel.Guard K γ))
    (trans (Kernel.guard-decode K γ)
      (trans (cong F (sym (Kernel.reify-decode K γ)))
        (sym (Kernel.guard-decode K (Kernel.reify K γ)))))

reify-body-decode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (γ : Kernel.Code K)
  → Kernel.decode K (Kernel.reify K (Kernel.Body K γ))
    ≡ Kernel.decode K (Kernel.Body K (Kernel.reify K γ))
reify-body-decode K γ =
  trans (Kernel.reify-decode K (Kernel.Body K γ))
    (trans (Kernel.body-decode K γ)
      (trans (cong (Kernel.Body∂ K) (sym (Kernel.reify-decode K γ)))
        (sym (Kernel.body-decode K (Kernel.reify K γ)))))

-- Factorization at decode-level: prefer Guard ∘ Body on the code layer.

decode-FlowCode-eq
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (γ : Kernel.Code K)
  → Kernel.decode K (FlowCode K γ)
    ≡ GTier.Flow (Kernel.G K) (GTier.step (Kernel.G K))
        (Kernel.Body∂ K (Kernel.decode K γ))
decode-FlowCode-eq = decode-FlowCode

-- ============================================================================
-- Trust helpers: make γ* fixed-point and FlowCode monotonicity explicit.
-- ============================================================================

-- Decode-level fixed-point inequalities for the one-step boundary functional
-- `c ↦ Flow (Body∂ c)` at the distinguished code `γ*`.

γ*-decode≤stepBody
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K))
      (Kernel.decode K (Kernel.γ* K))
      (GTier.Flow (Kernel.G K) (GTier.step (Kernel.G K))
        (Kernel.Body∂ K (Kernel.decode K (Kernel.γ* K))))
γ*-decode≤stepBody K =
  let
    CP = BulkBoundary.bnd (Kernel.BB K)
    open Kernel K
    le = Kernel.γ*-guard⇒ K
    eq = decode-FlowCode-eq K (Kernel.γ* K)
  in subst (λ x → ConPreorder._⊑_ CP (Kernel.decode K (Kernel.γ* K)) x) eq le

stepBody≤γ*-decode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K))
      (GTier.Flow (Kernel.G K) (GTier.step (Kernel.G K))
        (Kernel.Body∂ K (Kernel.decode K (Kernel.γ* K))))
      (Kernel.decode K (Kernel.γ* K))
stepBody≤γ*-decode K =
  let
    CP = BulkBoundary.bnd (Kernel.BB K)
    open Kernel K
    le = Kernel.γ*-guard⇐ K
    eq = decode-FlowCode-eq K (Kernel.γ* K)
  in subst (λ x → ConPreorder._⊑_ CP x (Kernel.decode K (Kernel.γ* K))) eq le

-- If the boundary preorder is antisymmetric (a partial order), γ* is an actual
-- equality fixed point at decode-level.

decode-FlowCode-γ*-eq
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → BulkBoundaryPO (Kernel.BB K)
  → ForKernel._≃K_ K (FlowCode K (Kernel.γ* K)) (Kernel.γ* K)
decode-FlowCode-γ*-eq K po =
  let
    open Kernel K
    open ForKernel K
    open BulkBoundaryPO po using (po-bnd)
    open PartialOrder po-bnd using (antisym)
    le₁ = Kernel.γ*-guard⇒ K
    le₂ = Kernel.γ*-guard⇐ K
  in antisym le₂ le₁

-- Optional: monotonicity of FlowCode at decode-level, assuming Body∂ is monotone.

decode-FlowCode-mono
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → KCore.BodyMonotoneShape (Kernel.shape K)
  → ∀ {γ δ}
  → ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K)) (Kernel.decode K γ) (Kernel.decode K δ)
  → ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K))
      (Kernel.decode K (FlowCode K γ))
      (Kernel.decode K (FlowCode K δ))
decode-FlowCode-mono {Sig = Sig} {Q = Q} K bm {γ} {δ} le =
  let
    open Kernel K
    CP = BulkBoundary.bnd (Kernel.BB K)
    F = GTier.Flow (Kernel.G K) (GTier.step (Kernel.G K))
    bodyLe = KCore.BodyMonotoneShape.mono-Body∂ bm le
    flowLe : ConPreorder._⊑_ CP (F (Kernel.Body∂ K (Kernel.decode K γ))) (F (Kernel.Body∂ K (Kernel.decode K δ)))
    flowLe = GTier.mono (Kernel.G K) bodyLe
    eqγ = decode-FlowCode-eq K γ
    eqδ = decode-FlowCode-eq K δ
    flowLe' : ConPreorder._⊑_ CP (F (Kernel.Body∂ K (Kernel.decode K γ))) (Kernel.decode K (FlowCode K δ))
    flowLe' = subst (λ x → ConPreorder._⊑_ CP (F (Kernel.Body∂ K (Kernel.decode K γ))) x) (sym eqδ) flowLe
  in subst (λ x → ConPreorder._⊑_ CP x (Kernel.decode K (FlowCode K δ))) (sym eqγ) flowLe'

-- Textbook alias: monotonicity of the operational step (FlowCode), under BodyMonotone.

flowcode-mono-decode = decode-FlowCode-mono

-- Code-level equivalence for reify (≈ in the code preorder).
-- This is the refinement counterpart to `reify-decode-eq`.

reify≈
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (γ : Kernel.Code K)
  → KCore.Code≈ (Kernel.shape K) (Kernel.reify K γ) γ
reify≈ K γ =
  let
    CP = BulkBoundary.bnd (Kernel.BB K)
    module R = ConRewrite.For CP
    eq = Kernel.reify-decode K γ
    reflCP = ConPreorder.refl CP
  in
  ( R.substL (sym eq) reflCP
  , R.substR (sym eq) reflCP
  )

-- Code-level monotonicity for FlowCode (no extra assumptions for kernels).

flowCode-mono
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → KCore.BodyMonotoneShape (Kernel.shape K)
  → ∀ {γ δ}
  → KCore.Code≤ (Kernel.shape K) γ δ
  → KCore.Code≤ (Kernel.shape K) (FlowCode K γ) (FlowCode K δ)
flowCode-mono K bm le = decode-FlowCode-mono K bm le
