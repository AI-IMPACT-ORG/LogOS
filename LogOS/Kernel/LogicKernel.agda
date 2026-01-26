{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.LogicKernel where

-- Generic kernel interface intended for the Curry–Howard–Lambek “single system”
-- view: an S/H/code kernel shape, together with a parameterised guarded (G) tier.
--
-- This module introduces no new axioms: it only repackages existing structures
-- (unguarded and graded) behind a shared interface, enabling uniform 2-categorical
-- refinements and irreversible (preorder-enriched) reasoning.

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
import LogOS.Minimal.Closure as Cl
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel.Core as Core hiding (FlowCode)

-- A minimal, “step-indexed” guarded tier over a boundary constraint preorder
-- (a poset once antisymmetry is supplied).
--
-- `Step` is:
-- - `⊤` for ungraded kernels (one global step),
-- - `Scale` for graded kernels (resource-indexed step),
-- but we keep it abstract so we can express both uniformly.
--
-- Only the saturation step `sat` is assumed to form a closure (mono/infl/idemp-lax),
-- matching existing `GuardedClosure` and `GradedClosure` interfaces.

record GTier {ℓ : Level} (Q : QAdapter ℓ) (CP : ConPreorder ℓ) : Set (lsuc ℓ) where
  open ConPreorder CP
  field
    Step : Set ℓ
    step : Step
    sat  : Step

    Flow : Step → Con → Con
    mono : ∀ {g c c'} → _⊑_ c c' → _⊑_ (Flow g c) (Flow g c')

    infl-sat  : ∀ c → _⊑_ c (Flow sat c)
    idemp-sat : ∀ c → _⊑_ (Flow sat (Flow sat c)) (Flow sat c)

    Th*       : Con
    Th*-fixed : (_⊑_ Th* (Flow sat Th*)) × (_⊑_ (Flow sat Th*) Th*)

open GTier public

-- A “logic kernel”: shared S/H/code shape + a parameterised guarded tier,
-- plus the coherence laws relating code-level `Guard` to the guarded step and
-- the distinguished decoded fixed point to `Th*`.

record LogicKernel {ℓ : Level} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
  : Set (lsuc (lsuc ℓ)) where
  field
    shape : Core.KernelShape Sig Q
  open Core.KernelShape shape public

  field
    shapeLaws : Core.KernelShapeLaws shape
  open Core.KernelShapeLaws shapeLaws public

  field
    G : GTier Q (BulkBoundary.bnd (Core.KernelShape.BB shape))

    guard-decode
      : ∀ γ →
        Core.KernelShape.decode shape (Core.KernelShape.Guard shape γ)
          ≡ GTier.Flow G (GTier.step G) (Core.KernelShape.decode shape γ)

    decode-γ*
      : Core.KernelShape.decode shape (Core.KernelShape.γ* shape)
        ≡ GTier.Th* G

StepOrder
  : ∀ {ℓ : Level}
    {Sig : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
  → Set ℓ
StepOrder K =
  ∀ c →
    ConPreorder._⊑_ (BulkBoundary.bnd (LogicKernel.BB K))
      (GTier.Flow (LogicKernel.G K) (GTier.step (LogicKernel.G K)) c)
      (GTier.Flow (LogicKernel.G K) (GTier.sat (LogicKernel.G K)) c)

-- Derived operational step on code: Guard ∘ Body (same as Kernel.FlowCode).

FlowCode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
  → LogicKernel.Code K → LogicKernel.Code K
FlowCode K = Core.FlowCode (LogicKernel.shape K)

decode-FlowCode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
    (γ : LogicKernel.Code K)
  → LogicKernel.decode K (FlowCode K γ)
    ≡ GTier.Flow (LogicKernel.G K) (GTier.step (LogicKernel.G K))
        (LogicKernel.Body∂ K (LogicKernel.decode K γ))
decode-FlowCode K γ =
  trans (LogicKernel.guard-decode K (LogicKernel.Body K γ))
        (cong (GTier.Flow (LogicKernel.G K) (GTier.step (LogicKernel.G K)))
              (LogicKernel.body-decode K γ))

guard-decode≤sat
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
    (step≤sat : StepOrder K)
    (γ : LogicKernel.Code K)
  → ConPreorder._⊑_ (BulkBoundary.bnd (LogicKernel.BB K))
      (LogicKernel.decode K (LogicKernel.Guard K γ))
      (GTier.Flow (LogicKernel.G K) (GTier.sat (LogicKernel.G K))
        (LogicKernel.decode K γ))
guard-decode≤sat K step≤sat γ =
  let
    CP = BulkBoundary.bnd (LogicKernel.BB K)
    le = step≤sat (LogicKernel.decode K γ)
    satFlow = GTier.Flow (LogicKernel.G K) (GTier.sat (LogicKernel.G K))
  in
  subst (λ x → ConPreorder._⊑_ CP x (satFlow (LogicKernel.decode K γ)))
        (sym (LogicKernel.guard-decode K γ))
        le

-- Stable closure modalities on code: encode ∘ Flow g ∘ decode.
--
-- `BoxAt` exposes bounded stabilization (step/resource g) on code.
-- `Box` is the saturation-step modality.

BoxAt
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
  → GTier.Step (LogicKernel.G K)
  → LogicKernel.Code K
  → LogicKernel.Code K
BoxAt K g γ =
  LogicKernel.encode K
    (GTier.Flow (LogicKernel.G K) g (LogicKernel.decode K γ))

decode-BoxAt
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
    (g : GTier.Step (LogicKernel.G K))
    (γ : LogicKernel.Code K)
  → LogicKernel.decode K (BoxAt K g γ)
      ≡ GTier.Flow (LogicKernel.G K) g (LogicKernel.decode K γ)
decode-BoxAt K g γ =
  LogicKernel.decode∘encode K
    (GTier.Flow (LogicKernel.G K) g (LogicKernel.decode K γ))

guard≈BoxAt-step
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
    (γ : LogicKernel.Code K)
  → Core.Code≈ (LogicKernel.shape K)
      (LogicKernel.Guard K γ)
      (BoxAt K (GTier.step (LogicKernel.G K)) γ)
guard≈BoxAt-step K γ = (guard≤BoxAt , boxAt≤Guard)
  where
    CP : ConPreorder _
    CP = BulkBoundary.bnd (LogicKernel.BB K)

    guard≤BoxAt
      : Core.Code≤ (LogicKernel.shape K)
          (LogicKernel.Guard K γ)
          (BoxAt K (GTier.step (LogicKernel.G K)) γ)
    guard≤BoxAt
      rewrite LogicKernel.guard-decode K γ
            | decode-BoxAt K (GTier.step (LogicKernel.G K)) γ
      = ConPreorder.refl CP

    boxAt≤Guard
      : Core.Code≤ (LogicKernel.shape K)
          (BoxAt K (GTier.step (LogicKernel.G K)) γ)
          (LogicKernel.Guard K γ)
    boxAt≤Guard
      rewrite decode-BoxAt K (GTier.step (LogicKernel.G K)) γ
            | LogicKernel.guard-decode K γ
      = ConPreorder.refl CP

Box
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
  → LogicKernel.Code K
  → LogicKernel.Code K
Box K = BoxAt K (GTier.sat (LogicKernel.G K))

decode-Box
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
    (γ : LogicKernel.Code K)
  → LogicKernel.decode K (Box K γ)
      ≡ GTier.Flow (LogicKernel.G K) (GTier.sat (LogicKernel.G K))
          (LogicKernel.decode K γ)
decode-Box K γ = decode-BoxAt K (GTier.sat (LogicKernel.G K)) γ

flowCode≈BoxAt-step-body
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
    (γ : LogicKernel.Code K)
  → Core.Code≈ (LogicKernel.shape K)
      (FlowCode K γ)
      (BoxAt K (GTier.step (LogicKernel.G K)) (LogicKernel.Body K γ))
flowCode≈BoxAt-step-body K γ = (flowCode≤BoxAtBody , boxAtBody≤FlowCode)
  where
    CP : ConPreorder _
    CP = BulkBoundary.bnd (LogicKernel.BB K)

    flowCode≤BoxAtBody
      : Core.Code≤ (LogicKernel.shape K)
          (FlowCode K γ)
          (BoxAt K (GTier.step (LogicKernel.G K)) (LogicKernel.Body K γ))
    flowCode≤BoxAtBody
      rewrite decode-FlowCode K γ
            | decode-BoxAt K (GTier.step (LogicKernel.G K)) (LogicKernel.Body K γ)
            | LogicKernel.body-decode K γ
      = ConPreorder.refl CP

    boxAtBody≤FlowCode
      : Core.Code≤ (LogicKernel.shape K)
          (BoxAt K (GTier.step (LogicKernel.G K)) (LogicKernel.Body K γ))
          (FlowCode K γ)
    boxAtBody≤FlowCode
      rewrite decode-BoxAt K (GTier.step (LogicKernel.G K)) (LogicKernel.Body K γ)
            | LogicKernel.body-decode K γ
            | decode-FlowCode K γ
      = ConPreorder.refl CP

decode-FlowCode≡decode-BoxAt-step-body
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
    (γ : LogicKernel.Code K)
  → LogicKernel.decode K (FlowCode K γ)
      ≡
      LogicKernel.decode K
        (BoxAt K (GTier.step (LogicKernel.G K)) (LogicKernel.Body K γ))
decode-FlowCode≡decode-BoxAt-step-body K γ
  rewrite decode-FlowCode K γ
        | decode-BoxAt K (GTier.step (LogicKernel.G K)) (LogicKernel.Body K γ)
        | LogicKernel.body-decode K γ
  = refl

boxAt-mono
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
    (g : GTier.Step (LogicKernel.G K))
  → ∀ {γ δ}
  → Core.Code≤ (LogicKernel.shape K) γ δ
  → Core.Code≤ (LogicKernel.shape K) (BoxAt K g γ) (BoxAt K g δ)
boxAt-mono K g {γ} {δ} le
  rewrite decode-BoxAt K g γ | decode-BoxAt K g δ
  = GTier.mono (LogicKernel.G K) le

box-mono
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
  → ∀ {γ δ}
  → Core.Code≤ (LogicKernel.shape K) γ δ
  → Core.Code≤ (LogicKernel.shape K) (Box K γ) (Box K δ)
box-mono K {γ} {δ} le = boxAt-mono K (GTier.sat (LogicKernel.G K)) le

decode-FlowCode≤sat
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
    (step≤sat : StepOrder K)
    (γ : LogicKernel.Code K)
  → ConPreorder._⊑_ (BulkBoundary.bnd (LogicKernel.BB K))
      (LogicKernel.decode K (FlowCode K γ))
      (GTier.Flow (LogicKernel.G K) (GTier.sat (LogicKernel.G K))
        (LogicKernel.Body∂ K (LogicKernel.decode K γ)))
decode-FlowCode≤sat K step≤sat γ
  rewrite decode-FlowCode K γ
  = step≤sat (LogicKernel.Body∂ K (LogicKernel.decode K γ))

guard≤Box
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
    (step≤sat : StepOrder K)
    (γ : LogicKernel.Code K)
  → Core.Code≤ (LogicKernel.shape K) (LogicKernel.Guard K γ) (Box K γ)
guard≤Box K step≤sat γ
  rewrite decode-Box K γ
  = guard-decode≤sat K step≤sat γ

flowCode≤BoxBody
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
    (step≤sat : StepOrder K)
    (γ : LogicKernel.Code K)
  → Core.Code≤ (LogicKernel.shape K) (FlowCode K γ) (Box K (LogicKernel.Body K γ))
flowCode≤BoxBody K step≤sat γ
  rewrite decode-Box K (LogicKernel.Body K γ)
        | LogicKernel.body-decode K γ
  = decode-FlowCode≤sat K step≤sat γ

box-infl
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
    (γ : LogicKernel.Code K)
  → Core.Code≤ (LogicKernel.shape K) γ (Box K γ)
box-infl K γ
  rewrite decode-Box K γ
  = GTier.infl-sat (LogicKernel.G K) (LogicKernel.decode K γ)

box-idemp-lax
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
    (γ : LogicKernel.Code K)
  → Core.Code≤ (LogicKernel.shape K) (Box K (Box K γ)) (Box K γ)
box-idemp-lax K γ
  rewrite decode-Box K (Box K γ) | decode-Box K γ
  = GTier.idemp-sat (LogicKernel.G K) (LogicKernel.decode K γ)

BoxClosure
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
  → Cl.ClosureOp (Core.CodePreorder (LogicKernel.shape K))
BoxClosure K =
  record
    { cl        = Box K
    ; mono      = box-mono K
    ; infl      = box-infl K
    ; idemp-lax = box-idemp-lax K
    }

-- Closed/stable fragment for the saturation modality `Box`.

BoxStable
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
  → LogicKernel.Code K → Set ℓ
BoxStable K γ = Core.Code≈ (LogicKernel.shape K) γ (Box K γ)

box-idemp
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
    (γ : LogicKernel.Code K)
  → Core.Code≈ (LogicKernel.shape K) (Box K γ) (Box K (Box K γ))
box-idemp K γ = Cl.idemp (BoxClosure K) γ

box-stable
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
    (γ : LogicKernel.Code K)
  → BoxStable K (Box K γ)
box-stable K γ = box-idemp K γ

-- Boundary closure induced by the saturation step.

SatClosure
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
  → Cl.ClosureOp (BulkBoundary.bnd (LogicKernel.BB K))
SatClosure K =
  record
    { cl        = GTier.Flow (LogicKernel.G K) (GTier.sat (LogicKernel.G K))
    ; mono      = λ {c} {c'} le →
                    GTier.mono (LogicKernel.G K) {g = GTier.sat (LogicKernel.G K)} le
    ; infl      = GTier.infl-sat (LogicKernel.G K)
    ; idemp-lax = GTier.idemp-sat (LogicKernel.G K)
    }

-- `decode` preserves the saturation stabilization: Box on code corresponds to
-- the saturation Flow on boundary constraints.

decode-BoxClosureHom
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
  → Cl.ClosureHomMono
      (Core.CodePreorder (LogicKernel.shape K))
      (BulkBoundary.bnd (LogicKernel.BB K))
      (BoxClosure K)
      (SatClosure K)
      (LogicKernel.decode K)
decode-BoxClosureHom K =
  Cl.mkClosureHomMono (Core.decode-mono (LogicKernel.shape K)) core
  where
    CP : ConPreorder _
    CP = BulkBoundary.bnd (LogicKernel.BB K)

    core : Cl.ClosureHom
            (Core.CodePreorder (LogicKernel.shape K))
            (BulkBoundary.bnd (LogicKernel.BB K))
            (BoxClosure K)
            (SatClosure K)
            (LogicKernel.decode K)
    core =
      record
        { preserves-cl = λ γ →
            subst (λ x →
                    ConPreorder._⊑_ CP x
                      (GTier.Flow (LogicKernel.G K) (GTier.sat (LogicKernel.G K))
                        (LogicKernel.decode K γ)))
                  (sym (decode-Box K γ))
                  (ConPreorder.refl CP)
        }

-- Stable code as a reflected sub-preorder (the “closed fragment”).

StableCode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
  → Set ℓ
StableCode K = Σ (LogicKernel.Code K) (BoxStable K)

StableCode≤
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
  → StableCode K → StableCode K → Set ℓ
StableCode≤ K x y = Core.Code≤ (LogicKernel.shape K) (proj₁ x) (proj₁ y)

StableCodePreorder
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
  → ConPreorder ℓ
StableCodePreorder K =
  record
    { Con   = StableCode K
    ; _⊑_   = StableCode≤ K
    ; refl  = ConPreorder.refl (Core.CodePreorder (LogicKernel.shape K))
    ; trans = ConPreorder.trans (Core.CodePreorder (LogicKernel.shape K))
    }

forgetStable
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
  → StableCode K → LogicKernel.Code K
forgetStable _ = proj₁

reflectBox
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
  → LogicKernel.Code K → StableCode K
reflectBox K γ = (Box K γ , box-stable K γ)

reflectBox-mono
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
  → ∀ {γ δ}
  → Core.Code≤ (LogicKernel.shape K) γ δ
  → StableCode≤ K (reflectBox K γ) (reflectBox K δ)
reflectBox-mono K le = box-mono K le

reflectBox-unit
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
    (γ : LogicKernel.Code K)
  → Core.Code≤ (LogicKernel.shape K) γ (forgetStable K (reflectBox K γ))
reflectBox-unit K γ = box-infl K γ

reflectBox-least
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
    {γ : LogicKernel.Code K}
    (δ : StableCode K)
  → Core.Code≤ (LogicKernel.shape K) γ (forgetStable K δ)
  → Core.Code≤ (LogicKernel.shape K) (forgetStable K (reflectBox K γ)) (forgetStable K δ)
reflectBox-least K {γ} δ γ≤δ =
  let
    CP = Core.CodePreorder (LogicKernel.shape K)
    boxδ≤δ = snd (proj₂ δ)
  in
  ConPreorder.trans CP (box-mono K γ≤δ) boxδ≤δ

γ*-box-fixed
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
  → Core.Code≤ (LogicKernel.shape K) (LogicKernel.γ* K) (Box K (LogicKernel.γ* K))
    ×
    Core.Code≤ (LogicKernel.shape K) (Box K (LogicKernel.γ* K)) (LogicKernel.γ* K)
γ*-box-fixed K
  rewrite decode-Box K (LogicKernel.γ* K) | LogicKernel.decode-γ* K
  = GTier.Th*-fixed (LogicKernel.G K)
