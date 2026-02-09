{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.UngradedKernel where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
import LogOS.Minimal.Closure as Cl
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel.Shape as Core hiding (FlowCode)

-- UngradedKernel = shared shape + ungraded guarded closure (G-tier).
--
-- The shared fields are factored out into `KernelShape` to avoid duplication with
-- graded kernels. We then “open” the shape publicly so the projection names stay
-- stable across the codebase.

record UngradedKernel {ℓ : Level} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
  : Set (lsuc (lsuc ℓ)) where
  field
    shape : Core.KernelShape Sig Q
  open Core.KernelShape shape public

  field
    -- G-tier: guarded closure on boundary constraints (stable truth).
    GTruth : Truth.GuardedCore.GuardedClosure (BulkBoundary.bnd (Core.KernelShape.BB shape))

    -- UngradedKernel coherence (laws) for the shared shape + guarded tier.
    laws : Core.KernelLaws shape GTruth

  open Core.KernelLaws laws public

-- Derived code-level Flow (Guard ∘ body)

FlowCode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q) → UngradedKernel.Code K → UngradedKernel.Code K
FlowCode K = Core.FlowCode (UngradedKernel.shape K)

decode-FlowCode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q) (γ : UngradedKernel.Code K)
  → UngradedKernel.decode K (FlowCode K γ)
    ≡ Truth.GuardedCore.GuardedClosure.Flow (UngradedKernel.GTruth K)
        (UngradedKernel.Body∂ K (UngradedKernel.decode K γ))
decode-FlowCode {Sig = Sig} {Q = Q} K γ =
  trans (UngradedKernel.guard-decode K (UngradedKernel.Body K γ))
        (cong (Truth.GuardedCore.GuardedClosure.Flow (UngradedKernel.GTruth K))
              (UngradedKernel.body-decode K γ))

-- Stable closure modality on code: encode ∘ Flow ∘ decode.

Box
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q) → UngradedKernel.Code K → UngradedKernel.Code K
Box K γ =
  UngradedKernel.encode K
    (Truth.GuardedCore.GuardedClosure.Flow (UngradedKernel.GTruth K) (UngradedKernel.decode K γ))

decode-Box
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q) (γ : UngradedKernel.Code K)
  → UngradedKernel.decode K (Box K γ)
      ≡ Truth.GuardedCore.GuardedClosure.Flow (UngradedKernel.GTruth K) (UngradedKernel.decode K γ)
decode-Box K γ =
  UngradedKernel.decode∘encode K
    (Truth.GuardedCore.GuardedClosure.Flow (UngradedKernel.GTruth K) (UngradedKernel.decode K γ))

box-mono
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q)
  → ∀ {γ δ}
  → Core.Code≤ (UngradedKernel.shape K) γ δ
  → Core.Code≤ (UngradedKernel.shape K) (Box K γ) (Box K δ)
box-mono K {γ} {δ} le
  rewrite decode-Box K γ | decode-Box K δ
  = UngradedKernel.mono-Flow K le

box-infl
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q)
    (γ : UngradedKernel.Code K)
  → Core.Code≤ (UngradedKernel.shape K) γ (Box K γ)
box-infl K γ
  rewrite decode-Box K γ
  = Truth.GuardedCore.GuardedClosure.infl (UngradedKernel.GTruth K) (UngradedKernel.decode K γ)

box-idemp-lax
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q)
    (γ : UngradedKernel.Code K)
  → Core.Code≤ (UngradedKernel.shape K) (Box K (Box K γ)) (Box K γ)
box-idemp-lax K γ
  rewrite decode-Box K (Box K γ) | decode-Box K γ
  = Truth.GuardedCore.GuardedClosure.idemp-lax (UngradedKernel.GTruth K) (UngradedKernel.decode K γ)

BoxClosure
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q)
  → Cl.ClosureOp (Core.CodePreorder (UngradedKernel.shape K))
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
    (K : UngradedKernel Sig Q)
  → UngradedKernel.Code K → Set ℓ
BoxStable K γ = Core.Code≈ (UngradedKernel.shape K) γ (Box K γ)

box-idemp
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q)
    (γ : UngradedKernel.Code K)
  → Core.Code≈ (UngradedKernel.shape K) (Box K γ) (Box K (Box K γ))
box-idemp K γ = Cl.idemp (BoxClosure K) γ

box-stable
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q)
    (γ : UngradedKernel.Code K)
  → BoxStable K (Box K γ)
box-stable K γ = box-idemp K γ

-- `decode` preserves the stabilization step: Box on code corresponds to Flow on
-- boundary constraints.

decode-BoxClosureHom
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q)
  → Cl.ClosureHomMono
      (Core.CodePreorder (UngradedKernel.shape K))
      (BulkBoundary.bnd (UngradedKernel.BB K))
      (BoxClosure K)
      (Truth.GuardedCore.closureOfGuardedClosure (UngradedKernel.GTruth K))
      (UngradedKernel.decode K)
decode-BoxClosureHom K =
  Cl.mkClosureHomMono (Core.decode-mono (UngradedKernel.shape K)) core
  where
    CP : ConPreorder _
    CP = BulkBoundary.bnd (UngradedKernel.BB K)

    core : Cl.ClosureHom
            (Core.CodePreorder (UngradedKernel.shape K))
            (BulkBoundary.bnd (UngradedKernel.BB K))
            (BoxClosure K)
            (Truth.GuardedCore.closureOfGuardedClosure (UngradedKernel.GTruth K))
            (UngradedKernel.decode K)
    core =
      record
        { preserves-cl = λ γ →
            let
              open Truth.GuardedCore.GuardedClosure (UngradedKernel.GTruth K) using (Flow)
            in
            subst (λ x → ConPreorder._⊑_ CP x (Flow (UngradedKernel.decode K γ)))
                  (sym (decode-Box K γ))
                  (ConPreorder.refl CP)
        }

-- Stable code as a reflected sub-preorder (the “closed fragment”).

StableCode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q)
  → Set ℓ
StableCode K = Σ (UngradedKernel.Code K) (BoxStable K)

StableCode≤
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q)
  → StableCode K → StableCode K → Set ℓ
StableCode≤ K x y = Core.Code≤ (UngradedKernel.shape K) (proj₁ x) (proj₁ y)

StableCodePreorder
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q)
  → ConPreorder ℓ
StableCodePreorder K =
  record
    { Con   = StableCode K
    ; _⊑_   = StableCode≤ K
    ; refl  = ConPreorder.refl (Core.CodePreorder (UngradedKernel.shape K))
    ; trans = ConPreorder.trans (Core.CodePreorder (UngradedKernel.shape K))
    }

forgetStable
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q)
  → StableCode K → UngradedKernel.Code K
forgetStable _ = proj₁

reflectBox
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q)
  → UngradedKernel.Code K → StableCode K
reflectBox K γ = (Box K γ , box-stable K γ)

reflectBox-mono
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q)
  → ∀ {γ δ}
  → Core.Code≤ (UngradedKernel.shape K) γ δ
  → StableCode≤ K (reflectBox K γ) (reflectBox K δ)
reflectBox-mono K le = box-mono K le

reflectBox-unit
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q)
    (γ : UngradedKernel.Code K)
  → Core.Code≤ (UngradedKernel.shape K) γ (forgetStable K (reflectBox K γ))
reflectBox-unit K γ = box-infl K γ

reflectBox-least
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q)
    {γ : UngradedKernel.Code K}
    (δ : StableCode K)
  → Core.Code≤ (UngradedKernel.shape K) γ (forgetStable K δ)
  → Core.Code≤ (UngradedKernel.shape K) (forgetStable K (reflectBox K γ)) (forgetStable K δ)
reflectBox-least K {γ} δ γ≤δ =
  let
    CP = Core.CodePreorder (UngradedKernel.shape K)
    boxδ≤δ = ≈CP⇐ {CP = CP} (proj₂ δ)
  in
  ConPreorder.trans CP (box-mono K γ≤δ) boxδ≤δ

guard≈Box
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q)
    (γ : UngradedKernel.Code K)
  → Core.Code≈ (UngradedKernel.shape K) (UngradedKernel.Guard K γ) (Box K γ)
guard≈Box K γ = (guard≤Box , box≤Guard)
  where
    CP : ConPreorder _
    CP = BulkBoundary.bnd (UngradedKernel.BB K)

    guard≤Box : Core.Code≤ (UngradedKernel.shape K) (UngradedKernel.Guard K γ) (Box K γ)
    guard≤Box
      rewrite UngradedKernel.guard-decode K γ | decode-Box K γ
      = ConPreorder.refl CP

    box≤Guard : Core.Code≤ (UngradedKernel.shape K) (Box K γ) (UngradedKernel.Guard K γ)
    box≤Guard
      rewrite decode-Box K γ | UngradedKernel.guard-decode K γ
      = ConPreorder.refl CP

flowCode≈BoxBody
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q)
    (γ : UngradedKernel.Code K)
  → Core.Code≈ (UngradedKernel.shape K) (FlowCode K γ) (Box K (UngradedKernel.Body K γ))
flowCode≈BoxBody K γ = (flowCode≤BoxBody , boxBody≤FlowCode)
  where
    CP : ConPreorder _
    CP = BulkBoundary.bnd (UngradedKernel.BB K)

    flowCode≤BoxBody : Core.Code≤ (UngradedKernel.shape K) (FlowCode K γ) (Box K (UngradedKernel.Body K γ))
    flowCode≤BoxBody
      rewrite decode-FlowCode K γ
            | decode-Box K (UngradedKernel.Body K γ)
            | UngradedKernel.body-decode K γ
      = ConPreorder.refl CP

    boxBody≤FlowCode : Core.Code≤ (UngradedKernel.shape K) (Box K (UngradedKernel.Body K γ)) (FlowCode K γ)
    boxBody≤FlowCode
      rewrite decode-Box K (UngradedKernel.Body K γ)
            | UngradedKernel.body-decode K γ
            | decode-FlowCode K γ
      = ConPreorder.refl CP

decode-FlowCode≡decode-BoxBody
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q)
    (γ : UngradedKernel.Code K)
  → UngradedKernel.decode K (FlowCode K γ) ≡ UngradedKernel.decode K (Box K (UngradedKernel.Body K γ))
decode-FlowCode≡decode-BoxBody K γ
  rewrite decode-FlowCode K γ
        | decode-Box K (UngradedKernel.Body K γ)
        | UngradedKernel.body-decode K γ
  = refl

γ*-box-fixed
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q)
  → Core.Code≤ (UngradedKernel.shape K) (UngradedKernel.γ* K) (Box K (UngradedKernel.γ* K))
    ×
    Core.Code≤ (UngradedKernel.shape K) (Box K (UngradedKernel.γ* K)) (UngradedKernel.γ* K)
γ*-box-fixed K
  rewrite decode-Box K (UngradedKernel.γ* K) | UngradedKernel.decode-γ* K
  = Truth.GuardedCore.GuardedClosure.Th*-fixed (UngradedKernel.GTruth K)
