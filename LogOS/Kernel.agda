{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
import LogOS.Minimal.Closure as Cl
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel.Core as Core hiding (FlowCode)
open import LogOS.Boundary.IO using (BoundaryIO; fromKernelShape)

-- Kernel = shared shape + ungraded guarded closure (G-tier).
--
-- The shared fields are factored out into `KernelShape` to avoid duplication with
-- graded kernels. We then “open” the shape publicly so the projection names stay
-- stable across the codebase.

record Kernel {ℓ : Level} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
  : Set (lsuc (lsuc ℓ)) where
  field
    shape : Core.KernelShape Sig Q
  open Core.KernelShape shape public

  field
    -- G-tier: guarded closure on boundary constraints (stable truth).
    GTruth : Truth.GuardedCore.GuardedClosure (BulkBoundary.bnd (Core.KernelShape.BB shape))

    -- Kernel coherence (laws) for the shared shape + guarded tier.
    laws : Core.KernelLaws shape GTruth

  open Core.KernelLaws laws public

-- Derived code-level Flow (Guard ∘ body)

FlowCode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q) → Kernel.Code K → Kernel.Code K
FlowCode K = Core.FlowCode (Kernel.shape K)

decode-FlowCode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q) (γ : Kernel.Code K)
  → Kernel.decode K (FlowCode K γ)
    ≡ Truth.GuardedCore.GuardedClosure.Flow (Kernel.GTruth K)
        (Kernel.Body∂ K (Kernel.decode K γ))
decode-FlowCode {Sig = Sig} {Q = Q} K γ =
  trans (Kernel.guard-decode K (Kernel.Body K γ))
        (cong (Truth.GuardedCore.GuardedClosure.Flow (Kernel.GTruth K))
              (Kernel.body-decode K γ))

-- Stable closure modality on code: encode ∘ Flow ∘ decode.

Box
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q) → Kernel.Code K → Kernel.Code K
Box K γ =
  Kernel.encode K
    (Truth.GuardedCore.GuardedClosure.Flow (Kernel.GTruth K) (Kernel.decode K γ))

decode-Box
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q) (γ : Kernel.Code K)
  → Kernel.decode K (Box K γ)
      ≡ Truth.GuardedCore.GuardedClosure.Flow (Kernel.GTruth K) (Kernel.decode K γ)
decode-Box K γ =
  Kernel.decode∘encode K
    (Truth.GuardedCore.GuardedClosure.Flow (Kernel.GTruth K) (Kernel.decode K γ))

box-mono
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → ∀ {γ δ}
  → Core.Code≤ (Kernel.shape K) γ δ
  → Core.Code≤ (Kernel.shape K) (Box K γ) (Box K δ)
box-mono K {γ} {δ} le
  rewrite decode-Box K γ | decode-Box K δ
  = Kernel.mono-Flow K le

box-infl
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (γ : Kernel.Code K)
  → Core.Code≤ (Kernel.shape K) γ (Box K γ)
box-infl K γ
  rewrite decode-Box K γ
  = Truth.GuardedCore.GuardedClosure.infl (Kernel.GTruth K) (Kernel.decode K γ)

box-idemp-lax
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (γ : Kernel.Code K)
  → Core.Code≤ (Kernel.shape K) (Box K (Box K γ)) (Box K γ)
box-idemp-lax K γ
  rewrite decode-Box K (Box K γ) | decode-Box K γ
  = Truth.GuardedCore.GuardedClosure.idemp-lax (Kernel.GTruth K) (Kernel.decode K γ)

BoxClosure
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → Cl.ClosureOp (Core.CodePreorder (Kernel.shape K))
BoxClosure K =
  record
    { cl        = Box K
    ; mono      = box-mono K
    ; infl      = box-infl K
    ; idemp-lax = box-idemp-lax K
    }

-- Closed/stable fragment for the Box modality: fixed points up to mutual refinement.

BoxStable
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → Kernel.Code K → Set ℓ
BoxStable K γ = Core.Code≈ (Kernel.shape K) γ (Box K γ)

box-idemp
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (γ : Kernel.Code K)
  → Core.Code≈ (Kernel.shape K) (Box K γ) (Box K (Box K γ))
box-idemp K γ = Cl.idemp (BoxClosure K) γ

box-stable
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (γ : Kernel.Code K)
  → BoxStable K (Box K γ)
box-stable K γ = box-idemp K γ

-- `decode` preserves the stabilization step: Box on code corresponds to Flow on
-- boundary constraints.

decode-BoxClosureHom
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → Cl.ClosureHomMono
      (Core.CodePreorder (Kernel.shape K))
      (BulkBoundary.bnd (Kernel.BB K))
      (BoxClosure K)
      (Truth.GuardedCore.closureOfGuardedClosure (Kernel.GTruth K))
      (Kernel.decode K)
decode-BoxClosureHom K =
  Cl.mkClosureHomMono (Core.decode-mono (Kernel.shape K)) core
  where
    CP : ConPreorder _
    CP = BulkBoundary.bnd (Kernel.BB K)

    core : Cl.ClosureHom
            (Core.CodePreorder (Kernel.shape K))
            (BulkBoundary.bnd (Kernel.BB K))
            (BoxClosure K)
            (Truth.GuardedCore.closureOfGuardedClosure (Kernel.GTruth K))
            (Kernel.decode K)
    core =
      record
        { preserves-cl = λ γ →
            let
              open Truth.GuardedCore.GuardedClosure (Kernel.GTruth K) using (Flow)
            in
            subst (λ x → ConPreorder._⊑_ CP x (Flow (Kernel.decode K γ)))
                  (sym (decode-Box K γ))
                  (ConPreorder.refl CP)
        }

-- Stable code as a reflected sub-preorder (the “closed fragment”).

StableCode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → Set ℓ
StableCode K = Σ (Kernel.Code K) (BoxStable K)

StableCode≤
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → StableCode K → StableCode K → Set ℓ
StableCode≤ K x y = Core.Code≤ (Kernel.shape K) (proj₁ x) (proj₁ y)

StableCodePreorder
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → ConPreorder ℓ
StableCodePreorder K =
  record
    { Con   = StableCode K
    ; _⊑_   = StableCode≤ K
    ; refl  = ConPreorder.refl (Core.CodePreorder (Kernel.shape K))
    ; trans = ConPreorder.trans (Core.CodePreorder (Kernel.shape K))
    }

forgetStable
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → StableCode K → Kernel.Code K
forgetStable _ = proj₁

reflectBox
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → Kernel.Code K → StableCode K
reflectBox K γ = (Box K γ , box-stable K γ)

reflectBox-mono
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → ∀ {γ δ}
  → Core.Code≤ (Kernel.shape K) γ δ
  → StableCode≤ K (reflectBox K γ) (reflectBox K δ)
reflectBox-mono K le = box-mono K le

reflectBox-unit
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (γ : Kernel.Code K)
  → Core.Code≤ (Kernel.shape K) γ (forgetStable K (reflectBox K γ))
reflectBox-unit K γ = box-infl K γ

reflectBox-least
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    {γ : Kernel.Code K}
    (δ : StableCode K)
  → Core.Code≤ (Kernel.shape K) γ (forgetStable K δ)
  → Core.Code≤ (Kernel.shape K) (forgetStable K (reflectBox K γ)) (forgetStable K δ)
reflectBox-least K {γ} δ γ≤δ =
  let
    CP = Core.CodePreorder (Kernel.shape K)
    boxδ≤δ = snd (proj₂ δ)
  in
  ConPreorder.trans CP (box-mono K γ≤δ) boxδ≤δ

guard≈Box
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (γ : Kernel.Code K)
  → Core.Code≈ (Kernel.shape K) (Kernel.Guard K γ) (Box K γ)
guard≈Box K γ = (guard≤Box , box≤Guard)
  where
    CP : ConPreorder _
    CP = BulkBoundary.bnd (Kernel.BB K)

    guard≤Box : Core.Code≤ (Kernel.shape K) (Kernel.Guard K γ) (Box K γ)
    guard≤Box
      rewrite Kernel.guard-decode K γ | decode-Box K γ
      = ConPreorder.refl CP

    box≤Guard : Core.Code≤ (Kernel.shape K) (Box K γ) (Kernel.Guard K γ)
    box≤Guard
      rewrite decode-Box K γ | Kernel.guard-decode K γ
      = ConPreorder.refl CP

flowCode≈BoxBody
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (γ : Kernel.Code K)
  → Core.Code≈ (Kernel.shape K) (FlowCode K γ) (Box K (Kernel.Body K γ))
flowCode≈BoxBody K γ = (flowCode≤BoxBody , boxBody≤FlowCode)
  where
    CP : ConPreorder _
    CP = BulkBoundary.bnd (Kernel.BB K)

    flowCode≤BoxBody : Core.Code≤ (Kernel.shape K) (FlowCode K γ) (Box K (Kernel.Body K γ))
    flowCode≤BoxBody
      rewrite decode-FlowCode K γ
            | decode-Box K (Kernel.Body K γ)
            | Kernel.body-decode K γ
      = ConPreorder.refl CP

    boxBody≤FlowCode : Core.Code≤ (Kernel.shape K) (Box K (Kernel.Body K γ)) (FlowCode K γ)
    boxBody≤FlowCode
      rewrite decode-Box K (Kernel.Body K γ)
            | Kernel.body-decode K γ
            | decode-FlowCode K γ
      = ConPreorder.refl CP

decode-FlowCode≡decode-BoxBody
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (γ : Kernel.Code K)
  → Kernel.decode K (FlowCode K γ) ≡ Kernel.decode K (Box K (Kernel.Body K γ))
decode-FlowCode≡decode-BoxBody K γ
  rewrite decode-FlowCode K γ
        | decode-Box K (Kernel.Body K γ)
        | Kernel.body-decode K γ
  = refl

γ*-box-fixed
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → Core.Code≤ (Kernel.shape K) (Kernel.γ* K) (Box K (Kernel.γ* K))
    ×
    Core.Code≤ (Kernel.shape K) (Box K (Kernel.γ* K)) (Kernel.γ* K)
γ*-box-fixed K
  rewrite decode-Box K (Kernel.γ* K) | Kernel.decode-γ* K
  = Truth.GuardedCore.GuardedClosure.Th*-fixed (Kernel.GTruth K)

-- Optional graded extension (kept under a separate namespace to avoid clashes).
import LogOS.Kernel.Graded as Gradedₜ
module Graded = Gradedₜ

import LogOS.Kernel.LogicKernel as LogicKernel

record KernelLike {ℓ : Level} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
  : Set (lsuc (lsuc ℓ)) where
  field
    shape : Core.KernelShape Sig Q
  open Core.KernelShape shape public

  boundaryIO
    : BoundaryIO Sig Q
        (Core.KernelShape.HWorld shape)
        (Core.KernelShape.BB shape)
        (Core.KernelShape.HTruth shape)
  boundaryIO = fromKernelShape shape

kernelLike-fromKernel
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  → Kernel Sig Q
  → KernelLike Sig Q
kernelLike-fromKernel K = record { shape = Kernel.shape K }

kernelLike-fromGraded
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  → Gradedₜ.GradedKernel Sig Q
  → KernelLike Sig Q
kernelLike-fromGraded K = record { shape = Gradedₜ.GradedKernel.shape K }

kernelLike-fromLogicKernel
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  → LogicKernel.LogicKernel Sig Q
  → KernelLike Sig Q
kernelLike-fromLogicKernel K = record { shape = LogicKernel.LogicKernel.shape K }
