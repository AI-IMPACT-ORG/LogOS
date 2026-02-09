{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel where

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
open import LogOS.Kernel.Shape as Core hiding (FlowCode)

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

  -- Canonical name: the chosen fixed point is fixed up to mutual refinement.
  Th*-fixed≈ : _≈CP_ CP Th* (Flow sat Th*)
  Th*-fixed≈ = Th*-fixed

  -- Directional projections.
  Th*-fixed⇒ : _⊑_ Th* (Flow sat Th*)
  Th*-fixed⇒ = ≈CP⇒ {CP = CP} Th*-fixed

  Th*-fixed⇐ : _⊑_ (Flow sat Th*) Th*
  Th*-fixed⇐ = ≈CP⇐ {CP = CP} Th*-fixed

open GTier public

-- A “logic kernel”: shared S/H/code shape + a parameterised guarded tier,
-- plus the coherence laws relating code-level `Guard` to the guarded step and
-- the distinguished decoded fixed point to `Th*`.

record Kernel {ℓ : Level} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
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

-- The induced (saturation) guarded closure on boundary constraints.
--
-- This is the canonical “G-truth” object used by boundary theorems: it forgets the
-- step-grade, keeping only the saturation closure and its chosen fixed point.

GTruth
  : ∀ {ℓ : Level}
    {Sig : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → Truth.GuardedCore.GuardedClosure (BulkBoundary.bnd (Kernel.BB K))
GTruth K =
  record
    { Flow      = λ c → GTier.Flow (Kernel.G K) (GTier.sat (Kernel.G K)) c
    ; mono      = λ {c} {c'} le →
                    GTier.mono (Kernel.G K) {g = GTier.sat (Kernel.G K)} le
    ; infl      = GTier.infl-sat (Kernel.G K)
    ; idemp-lax = GTier.idemp-sat (Kernel.G K)
    ; Th*       = GTier.Th* (Kernel.G K)
    ; Th*-fixed = GTier.Th*-fixed (Kernel.G K)
    }

StepOrder
  : ∀ {ℓ : Level}
    {Sig : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → Set ℓ
StepOrder K =
  ∀ c →
    ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K))
      (GTier.Flow (Kernel.G K) (GTier.step (Kernel.G K)) c)
      (GTier.Flow (Kernel.G K) (GTier.sat (Kernel.G K)) c)

-- Derived operational step on code: Guard ∘ Body (same as Kernel.FlowCode).

FlowCode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → Kernel.Code K → Kernel.Code K
FlowCode K = Core.FlowCode (Kernel.shape K)

decode-FlowCode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (γ : Kernel.Code K)
  → Kernel.decode K (FlowCode K γ)
    ≡ GTier.Flow (Kernel.G K) (GTier.step (Kernel.G K))
        (Kernel.Body∂ K (Kernel.decode K γ))
decode-FlowCode K γ =
  trans (Kernel.guard-decode K (Kernel.Body K γ))
        (cong (GTier.Flow (Kernel.G K) (GTier.step (Kernel.G K)))
              (Kernel.body-decode K γ))

guard-decode≤sat
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (step≤sat : StepOrder K)
    (γ : Kernel.Code K)
  → ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K))
      (Kernel.decode K (Kernel.Guard K γ))
      (GTier.Flow (Kernel.G K) (GTier.sat (Kernel.G K))
        (Kernel.decode K γ))
guard-decode≤sat K step≤sat γ =
  let
    CP = BulkBoundary.bnd (Kernel.BB K)
    le = step≤sat (Kernel.decode K γ)
    satFlow = GTier.Flow (Kernel.G K) (GTier.sat (Kernel.G K))
  in
  subst (λ x → ConPreorder._⊑_ CP x (satFlow (Kernel.decode K γ)))
        (sym (Kernel.guard-decode K γ))
        le

-- Stable closure modalities on code: encode ∘ Flow g ∘ decode.
--
-- `BoxAt` exposes bounded stabilization (step/resource g) on code.
-- `Box` is the saturation-step modality.

BoxAt
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → GTier.Step (Kernel.G K)
  → Kernel.Code K
  → Kernel.Code K
BoxAt K g γ =
  Kernel.encode K
    (GTier.Flow (Kernel.G K) g (Kernel.decode K γ))

decode-BoxAt
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (g : GTier.Step (Kernel.G K))
    (γ : Kernel.Code K)
  → Kernel.decode K (BoxAt K g γ)
      ≡ GTier.Flow (Kernel.G K) g (Kernel.decode K γ)
decode-BoxAt K g γ =
  Kernel.decode∘encode K
    (GTier.Flow (Kernel.G K) g (Kernel.decode K γ))

-- Port-style “quine” (scrunched): print to boundary (`decode`), read back (`encode`).
module PortQuine
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  where
  ∂Con : Set ℓ
  ∂Con = ConPreorder.Con (BulkBoundary.bnd (Kernel.BB K))

  emit : Kernel.Code K → ∂Con
  emit = Kernel.decode K

  compile : ∂Con → Kernel.Code K
  compile = Kernel.encode K

  quineStep : Kernel.Code K → Kernel.Code K
  quineStep γ = compile (emit γ)

  emit-quineStep : ∀ γ → emit (quineStep γ) ≡ emit γ
  emit-quineStep γ = Kernel.decode∘encode K (emit γ)

  -- “Self-production under refinement”: quineStep is the identity on code up to
  -- decoded mutual refinement (`Code≈`), not strict Agda equality.
  quineStep≈ : ∀ γ → Core.Code≈ (Kernel.shape K) (quineStep γ) γ
  quineStep≈ γ rewrite emit-quineStep γ = (ConPreorder.refl CP , ConPreorder.refl CP)
    where
      CP = BulkBoundary.bnd (Kernel.BB K)

  roundtrip∂ : ∂Con → ∂Con
  roundtrip∂ c = emit (compile c)

  roundtrip∂-id : ∀ c → roundtrip∂ c ≡ c
  roundtrip∂-id = Kernel.decode∘encode K

guard≈BoxAt-step
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (γ : Kernel.Code K)
  → Core.Code≈ (Kernel.shape K)
      (Kernel.Guard K γ)
      (BoxAt K (GTier.step (Kernel.G K)) γ)
guard≈BoxAt-step K γ = (guard≤BoxAt , boxAt≤Guard)
  where
    CP : ConPreorder _
    CP = BulkBoundary.bnd (Kernel.BB K)

    guard≤BoxAt
      : Core.Code≤ (Kernel.shape K)
          (Kernel.Guard K γ)
          (BoxAt K (GTier.step (Kernel.G K)) γ)
    guard≤BoxAt
      rewrite Kernel.guard-decode K γ
            | decode-BoxAt K (GTier.step (Kernel.G K)) γ
      = ConPreorder.refl CP

    boxAt≤Guard
      : Core.Code≤ (Kernel.shape K)
          (BoxAt K (GTier.step (Kernel.G K)) γ)
          (Kernel.Guard K γ)
    boxAt≤Guard
      rewrite decode-BoxAt K (GTier.step (Kernel.G K)) γ
            | Kernel.guard-decode K γ
      = ConPreorder.refl CP

Box
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → Kernel.Code K
  → Kernel.Code K
Box K = BoxAt K (GTier.sat (Kernel.G K))

decode-Box
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (γ : Kernel.Code K)
  → Kernel.decode K (Box K γ)
      ≡ GTier.Flow (Kernel.G K) (GTier.sat (Kernel.G K))
          (Kernel.decode K γ)
decode-Box K γ = decode-BoxAt K (GTier.sat (Kernel.G K)) γ

flowCode≈BoxAt-step-body
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (γ : Kernel.Code K)
  → Core.Code≈ (Kernel.shape K)
      (FlowCode K γ)
      (BoxAt K (GTier.step (Kernel.G K)) (Kernel.Body K γ))
flowCode≈BoxAt-step-body K γ = (flowCode≤BoxAtBody , boxAtBody≤FlowCode)
  where
    CP : ConPreorder _
    CP = BulkBoundary.bnd (Kernel.BB K)

    flowCode≤BoxAtBody
      : Core.Code≤ (Kernel.shape K)
          (FlowCode K γ)
          (BoxAt K (GTier.step (Kernel.G K)) (Kernel.Body K γ))
    flowCode≤BoxAtBody
      rewrite decode-FlowCode K γ
            | decode-BoxAt K (GTier.step (Kernel.G K)) (Kernel.Body K γ)
            | Kernel.body-decode K γ
      = ConPreorder.refl CP

    boxAtBody≤FlowCode
      : Core.Code≤ (Kernel.shape K)
          (BoxAt K (GTier.step (Kernel.G K)) (Kernel.Body K γ))
          (FlowCode K γ)
    boxAtBody≤FlowCode
      rewrite decode-BoxAt K (GTier.step (Kernel.G K)) (Kernel.Body K γ)
            | Kernel.body-decode K γ
            | decode-FlowCode K γ
      = ConPreorder.refl CP

decode-FlowCode≡decode-BoxAt-step-body
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (γ : Kernel.Code K)
  → Kernel.decode K (FlowCode K γ)
      ≡
      Kernel.decode K
        (BoxAt K (GTier.step (Kernel.G K)) (Kernel.Body K γ))
decode-FlowCode≡decode-BoxAt-step-body K γ
  rewrite decode-FlowCode K γ
        | decode-BoxAt K (GTier.step (Kernel.G K)) (Kernel.Body K γ)
        | Kernel.body-decode K γ
  = refl

boxAt-mono
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (g : GTier.Step (Kernel.G K))
  → ∀ {γ δ}
  → Core.Code≤ (Kernel.shape K) γ δ
  → Core.Code≤ (Kernel.shape K) (BoxAt K g γ) (BoxAt K g δ)
boxAt-mono K g {γ} {δ} le
  rewrite decode-BoxAt K g γ | decode-BoxAt K g δ
  = GTier.mono (Kernel.G K) le

box-mono
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → ∀ {γ δ}
  → Core.Code≤ (Kernel.shape K) γ δ
  → Core.Code≤ (Kernel.shape K) (Box K γ) (Box K δ)
box-mono K {γ} {δ} le = boxAt-mono K (GTier.sat (Kernel.G K)) le

decode-FlowCode≤sat
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (step≤sat : StepOrder K)
    (γ : Kernel.Code K)
  → ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K))
      (Kernel.decode K (FlowCode K γ))
      (GTier.Flow (Kernel.G K) (GTier.sat (Kernel.G K))
        (Kernel.Body∂ K (Kernel.decode K γ)))
decode-FlowCode≤sat K step≤sat γ
  rewrite decode-FlowCode K γ
  = step≤sat (Kernel.Body∂ K (Kernel.decode K γ))

guard≤Box
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (step≤sat : StepOrder K)
    (γ : Kernel.Code K)
  → Core.Code≤ (Kernel.shape K) (Kernel.Guard K γ) (Box K γ)
guard≤Box K step≤sat γ
  rewrite decode-Box K γ
  = guard-decode≤sat K step≤sat γ

flowCode≤BoxBody
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (step≤sat : StepOrder K)
    (γ : Kernel.Code K)
  → Core.Code≤ (Kernel.shape K) (FlowCode K γ) (Box K (Kernel.Body K γ))
flowCode≤BoxBody K step≤sat γ
  rewrite decode-Box K (Kernel.Body K γ)
        | Kernel.body-decode K γ
  = decode-FlowCode≤sat K step≤sat γ

box-infl
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (γ : Kernel.Code K)
  → Core.Code≤ (Kernel.shape K) γ (Box K γ)
box-infl K γ
  rewrite decode-Box K γ
  = GTier.infl-sat (Kernel.G K) (Kernel.decode K γ)

box-idemp-lax
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (γ : Kernel.Code K)
  → Core.Code≤ (Kernel.shape K) (Box K (Box K γ)) (Box K γ)
box-idemp-lax K γ
  rewrite decode-Box K (Box K γ) | decode-Box K γ
  = GTier.idemp-sat (Kernel.G K) (Kernel.decode K γ)

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

-- Closed/stable fragment for the saturation modality `Box`.

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

-- Boundary closure induced by the saturation step.

SatClosure
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → Cl.ClosureOp (BulkBoundary.bnd (Kernel.BB K))
SatClosure K =
  record
    { cl        = GTier.Flow (Kernel.G K) (GTier.sat (Kernel.G K))
    ; mono      = λ {c} {c'} le →
                    GTier.mono (Kernel.G K) {g = GTier.sat (Kernel.G K)} le
    ; infl      = GTier.infl-sat (Kernel.G K)
    ; idemp-lax = GTier.idemp-sat (Kernel.G K)
    }

-- `decode` preserves the saturation stabilization: Box on code corresponds to
-- the saturation Flow on boundary constraints.

decode-BoxClosureHom
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → Cl.ClosureHomMono
      (Core.CodePreorder (Kernel.shape K))
      (BulkBoundary.bnd (Kernel.BB K))
      (BoxClosure K)
      (SatClosure K)
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
            (SatClosure K)
            (Kernel.decode K)
    core =
      record
        { preserves-cl = λ γ →
            subst (λ x →
                    ConPreorder._⊑_ CP x
                      (GTier.Flow (Kernel.G K) (GTier.sat (Kernel.G K))
                        (Kernel.decode K γ)))
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

γ*-box-fixed
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → Core.Code≤ (Kernel.shape K) (Kernel.γ* K) (Box K (Kernel.γ* K))
    ×
    Core.Code≤ (Kernel.shape K) (Box K (Kernel.γ* K)) (Kernel.γ* K)
γ*-box-fixed K
  rewrite decode-Box K (Kernel.γ* K) | Kernel.decode-γ* K
  = GTier.Th*-fixed (Kernel.G K)

-- A “shape-only” kernel view: shared S/H/code layer without assuming any
-- guarded truth tier. This is the right interface for APIs that only need
-- code/decode/reify and constraint structure.

record KernelLike {ℓ : Level} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
  : Set (lsuc (lsuc ℓ)) where
  field
    shape : Core.KernelShape Sig Q
  open Core.KernelShape shape public

kernelLike-fromKernel
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  → Kernel Sig Q
  → KernelLike Sig Q
kernelLike-fromKernel K = record { shape = Kernel.shape K }
