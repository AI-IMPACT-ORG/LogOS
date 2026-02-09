{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Graded where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
import LogOS.Minimal.Closure as Cl
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel.Shape as Core hiding (FlowCode)

open Truth.GuardedCore public using
  ( GradedClosure
  ; GradeHom
  ; GradedFlowHom
  ; GradedFlowHomWithGrade
  ; forgetGradedClosure
  )

-- Graded kernel: same shared shape as `Kernel`, but guarded flow is grade-indexed.
record GradedKernel {ℓ : Level} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
  : Set (lsuc (lsuc ℓ)) where
  field
    shape : Core.KernelShape Sig Q
  open Core.KernelShape shape public

  field
    shapeLaws : Core.KernelShapeLaws shape
  open Core.KernelShapeLaws shapeLaws public

  field
    -- G-tier: graded guarded closure on boundary constraints
    GTruth     : GradedClosure Q (BulkBoundary.bnd (Core.KernelShape.BB shape))
    step-grade : QAdapter.Scale Q

    -- Kernel coherence: `Guard` internalises the one-step (step-grade) flow at decode level.
    guard-decode
      : ∀ γ
      → Core.KernelShape.decode shape (Core.KernelShape.Guard shape γ)
        ≡ GradedClosure.Flow GTruth step-grade (Core.KernelShape.decode shape γ)

    -- Distinguished code witness decodes to the saturation-grade fixed point.
    decode-γ* : Core.KernelShape.decode shape (Core.KernelShape.γ* shape) ≡ GradedClosure.Th* GTruth

-- Derived code-level Flow (Guard ∘ Body).
FlowCode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q) → GradedKernel.Code K → GradedKernel.Code K
FlowCode K = Core.FlowCode (GradedKernel.shape K)

decode-FlowCode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q) (γ : GradedKernel.Code K)
  → GradedKernel.decode K (FlowCode K γ)
    ≡ GradedClosure.Flow (GradedKernel.GTruth K) (GradedKernel.step-grade K)
        (GradedKernel.Body∂ K (GradedKernel.decode K γ))
decode-FlowCode {Sig = Sig} {Q = Q} K γ =
  trans (GradedKernel.guard-decode K (GradedKernel.Body K γ))
        (cong (GradedClosure.Flow (GradedKernel.GTruth K) (GradedKernel.step-grade K))
              (GradedKernel.body-decode K γ))

-- Step-grade vs saturation-grade friction reducers.
--
-- In a graded kernel, `Guard` decodes to a one-step `Flow step-grade`, while the
-- distinguished fixed-point witness `Th*` lives at the saturation grade. The following
-- derived lemmas make the grade shift explicit and help avoid accidental
-- rewrites of step-grade facts as saturation facts.

-- Step-grade is always ≤ saturation grade (derived from `sat-top`).
step≤sat
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → QAdapter._≤s_ Q (GradedKernel.step-grade K) (GradedClosure.sat (GradedKernel.GTruth K))
step≤sat K = GradedClosure.sat-top (GradedKernel.GTruth K) (GradedKernel.step-grade K)

guard-decode≤sat
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q) (γ : GradedKernel.Code K)
  → ConPreorder._⊑_ (BulkBoundary.bnd (GradedKernel.BB K))
      (GradedKernel.decode K (GradedKernel.Guard K γ))
      (GradedClosure.Flow (GradedKernel.GTruth K) (GradedClosure.sat (GradedKernel.GTruth K))
        (GradedKernel.decode K γ))
guard-decode≤sat K γ =
  let open GradedKernel K
      CP = BulkBoundary.bnd (GradedKernel.BB K)
      le = GradedClosure.mono-grade GTruth (step≤sat K) (GradedKernel.decode K γ)
  in subst (λ x → ConPreorder._⊑_ CP x (GradedClosure.Flow GTruth (GradedClosure.sat GTruth) (GradedKernel.decode K γ)))
           (sym (guard-decode γ))
           le

decode-FlowCode≤sat
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q) (γ : GradedKernel.Code K)
  → ConPreorder._⊑_ (BulkBoundary.bnd (GradedKernel.BB K))
      (GradedKernel.decode K (FlowCode K γ))
      (GradedClosure.Flow (GradedKernel.GTruth K) (GradedClosure.sat (GradedKernel.GTruth K))
        (GradedKernel.Body∂ K (GradedKernel.decode K γ)))
decode-FlowCode≤sat K γ =
  let open GradedKernel K
      CP = BulkBoundary.bnd (GradedKernel.BB K)
      le = GradedClosure.mono-grade GTruth (step≤sat K) (GradedKernel.Body∂ K (GradedKernel.decode K γ))
  in subst (λ x → ConPreorder._⊑_ CP x (GradedClosure.Flow GTruth (GradedClosure.sat GTruth) (GradedKernel.Body∂ K (GradedKernel.decode K γ))))
           (sym (decode-FlowCode K γ))
           le

-- Stable closure modalities on code: encode ∘ Flow g ∘ decode.
--
-- `BoxAt` exposes bounded stabilization (grade/budget g) on code.
-- `Box` is the saturation-grade (cost → ∞) modality.

BoxAt
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → QAdapter.Scale Q
  → GradedKernel.Code K
  → GradedKernel.Code K
BoxAt {Q = Q} K g γ =
  GradedKernel.encode K
    (GradedClosure.Flow (GradedKernel.GTruth K) g (GradedKernel.decode K γ))

decode-BoxAt
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (g : QAdapter.Scale Q)
    (γ : GradedKernel.Code K)
  → GradedKernel.decode K (BoxAt K g γ)
      ≡ GradedClosure.Flow (GradedKernel.GTruth K) g (GradedKernel.decode K γ)
decode-BoxAt {Q = Q} K g γ =
  GradedKernel.decode∘encode K
    (GradedClosure.Flow (GradedKernel.GTruth K) g (GradedKernel.decode K γ))

guard≈BoxAt-step
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (γ : GradedKernel.Code K)
  → Core.Code≈ (GradedKernel.shape K)
      (GradedKernel.Guard K γ)
      (BoxAt K (GradedKernel.step-grade K) γ)
guard≈BoxAt-step K γ = (guard≤BoxAt , boxAt≤Guard)
  where
    CP : ConPreorder _
    CP = BulkBoundary.bnd (GradedKernel.BB K)

    guard≤BoxAt
      : Core.Code≤ (GradedKernel.shape K)
          (GradedKernel.Guard K γ)
          (BoxAt K (GradedKernel.step-grade K) γ)
    guard≤BoxAt
      rewrite GradedKernel.guard-decode K γ
            | decode-BoxAt K (GradedKernel.step-grade K) γ
      = ConPreorder.refl CP

    boxAt≤Guard
      : Core.Code≤ (GradedKernel.shape K)
          (BoxAt K (GradedKernel.step-grade K) γ)
          (GradedKernel.Guard K γ)
    boxAt≤Guard
      rewrite decode-BoxAt K (GradedKernel.step-grade K) γ
            | GradedKernel.guard-decode K γ
      = ConPreorder.refl CP

Box
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → GradedKernel.Code K
  → GradedKernel.Code K
Box K = BoxAt K (GradedClosure.sat (GradedKernel.GTruth K))

decode-Box
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (γ : GradedKernel.Code K)
  → GradedKernel.decode K (Box K γ)
      ≡ GradedClosure.Flow (GradedKernel.GTruth K) (GradedClosure.sat (GradedKernel.GTruth K))
          (GradedKernel.decode K γ)
decode-Box K γ = decode-BoxAt K (GradedClosure.sat (GradedKernel.GTruth K)) γ

flowCode≈BoxAt-step-body
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (γ : GradedKernel.Code K)
  → Core.Code≈ (GradedKernel.shape K)
      (FlowCode K γ)
      (BoxAt K (GradedKernel.step-grade K) (GradedKernel.Body K γ))
flowCode≈BoxAt-step-body K γ = (flowCode≤BoxAtBody , boxAtBody≤FlowCode)
  where
    CP : ConPreorder _
    CP = BulkBoundary.bnd (GradedKernel.BB K)

    flowCode≤BoxAtBody
      : Core.Code≤ (GradedKernel.shape K)
          (FlowCode K γ)
          (BoxAt K (GradedKernel.step-grade K) (GradedKernel.Body K γ))
    flowCode≤BoxAtBody
      rewrite decode-FlowCode K γ
            | decode-BoxAt K (GradedKernel.step-grade K) (GradedKernel.Body K γ)
            | GradedKernel.body-decode K γ
      = ConPreorder.refl CP

    boxAtBody≤FlowCode
      : Core.Code≤ (GradedKernel.shape K)
          (BoxAt K (GradedKernel.step-grade K) (GradedKernel.Body K γ))
          (FlowCode K γ)
    boxAtBody≤FlowCode
      rewrite decode-BoxAt K (GradedKernel.step-grade K) (GradedKernel.Body K γ)
            | GradedKernel.body-decode K γ
            | decode-FlowCode K γ
      = ConPreorder.refl CP

decode-FlowCode≡decode-BoxAt-step-body
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (γ : GradedKernel.Code K)
  → GradedKernel.decode K (FlowCode K γ)
      ≡
      GradedKernel.decode K
        (BoxAt K (GradedKernel.step-grade K) (GradedKernel.Body K γ))
decode-FlowCode≡decode-BoxAt-step-body K γ
  rewrite decode-FlowCode K γ
        | decode-BoxAt K (GradedKernel.step-grade K) (GradedKernel.Body K γ)
        | GradedKernel.body-decode K γ
  = refl

boxAt-mono
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (g : QAdapter.Scale Q)
  → ∀ {γ δ}
  → Core.Code≤ (GradedKernel.shape K) γ δ
  → Core.Code≤ (GradedKernel.shape K) (BoxAt K g γ) (BoxAt K g δ)
boxAt-mono K g {γ} {δ} le
  rewrite decode-BoxAt K g γ | decode-BoxAt K g δ
  = GradedClosure.mono (GradedKernel.GTruth K) {g = g} le

boxAt-comp-lax
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (g g' : QAdapter.Scale Q)
    (γ : GradedKernel.Code K)
  → Core.Code≤ (GradedKernel.shape K)
      (BoxAt K g' (BoxAt K g γ))
      (BoxAt K (QAdapter._·_ Q g g') γ)
boxAt-comp-lax {Q = Q} K g g' γ
  rewrite decode-BoxAt K g' (BoxAt K g γ)
        | decode-BoxAt K g γ
        | decode-BoxAt K (QAdapter._·_ Q g g') γ
  = GradedClosure.comp-lax (GradedKernel.GTruth K) g g' (GradedKernel.decode K γ)

box-mono
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → ∀ {γ δ}
  → Core.Code≤ (GradedKernel.shape K) γ δ
  → Core.Code≤ (GradedKernel.shape K) (Box K γ) (Box K δ)
box-mono K {γ} {δ} le =
  boxAt-mono K (GradedClosure.sat (GradedKernel.GTruth K)) le

guard≤Box
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (γ : GradedKernel.Code K)
  → Core.Code≤ (GradedKernel.shape K) (GradedKernel.Guard K γ) (Box K γ)
guard≤Box K γ
  rewrite decode-Box K γ
  = guard-decode≤sat K γ

flowCode≤BoxBody
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (γ : GradedKernel.Code K)
  → Core.Code≤ (GradedKernel.shape K) (FlowCode K γ) (Box K (GradedKernel.Body K γ))
flowCode≤BoxBody K γ
  rewrite decode-Box K (GradedKernel.Body K γ)
        | GradedKernel.body-decode K γ
  = decode-FlowCode≤sat K γ

box-infl
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (γ : GradedKernel.Code K)
  → Core.Code≤ (GradedKernel.shape K) γ (Box K γ)
box-infl K γ
  rewrite decode-Box K γ
  = GradedClosure.infl-sat (GradedKernel.GTruth K) (GradedKernel.decode K γ)

box-idemp-lax
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (γ : GradedKernel.Code K)
  → Core.Code≤ (GradedKernel.shape K) (Box K (Box K γ)) (Box K γ)
box-idemp-lax K γ
  rewrite decode-Box K (Box K γ) | decode-Box K γ
  = GradedClosure.idemp-sat (GradedKernel.GTruth K) (GradedKernel.decode K γ)

BoxClosure
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → Cl.ClosureOp (Core.CodePreorder (GradedKernel.shape K))
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
    (K : GradedKernel Sig Q)
  → GradedKernel.Code K → Set ℓ
BoxStable K γ = Core.Code≈ (GradedKernel.shape K) γ (Box K γ)

box-idemp
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (γ : GradedKernel.Code K)
  → Core.Code≈ (GradedKernel.shape K) (Box K γ) (Box K (Box K γ))
box-idemp K γ = Cl.idemp (BoxClosure K) γ

box-stable
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (γ : GradedKernel.Code K)
  → BoxStable K (Box K γ)
box-stable K γ = box-idemp K γ

-- `decode` preserves the saturation stabilization: Box on code corresponds to
-- the saturation Flow on boundary constraints.

decode-BoxClosureHom
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → Cl.ClosureHomMono
      (Core.CodePreorder (GradedKernel.shape K))
      (BulkBoundary.bnd (GradedKernel.BB K))
      (BoxClosure K)
      (Truth.GuardedCore.closureOfGradedClosure-sat (GradedKernel.GTruth K))
      (GradedKernel.decode K)
decode-BoxClosureHom K =
  Cl.mkClosureHomMono (Core.decode-mono (GradedKernel.shape K)) core
  where
    CP : ConPreorder _
    CP = BulkBoundary.bnd (GradedKernel.BB K)

    core : Cl.ClosureHom
            (Core.CodePreorder (GradedKernel.shape K))
            (BulkBoundary.bnd (GradedKernel.BB K))
            (BoxClosure K)
            (Truth.GuardedCore.closureOfGradedClosure-sat (GradedKernel.GTruth K))
            (GradedKernel.decode K)
    core =
      record
        { preserves-cl = λ γ →
            let
              open Truth.GuardedCore.GradedClosure (GradedKernel.GTruth K) using (Flow; sat)
            in
            subst (λ x → ConPreorder._⊑_ CP x (Flow sat (GradedKernel.decode K γ)))
                  (sym (decode-Box K γ))
                  (ConPreorder.refl CP)
        }

-- Stable code as a reflected sub-preorder (the “closed fragment”).

StableCode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → Set ℓ
StableCode K = Σ (GradedKernel.Code K) (BoxStable K)

StableCode≤
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → StableCode K → StableCode K → Set ℓ
StableCode≤ K x y = Core.Code≤ (GradedKernel.shape K) (proj₁ x) (proj₁ y)

StableCodePreorder
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → ConPreorder ℓ
StableCodePreorder K =
  record
    { Con   = StableCode K
    ; _⊑_   = StableCode≤ K
    ; refl  = ConPreorder.refl (Core.CodePreorder (GradedKernel.shape K))
    ; trans = ConPreorder.trans (Core.CodePreorder (GradedKernel.shape K))
    }

forgetStable
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → StableCode K → GradedKernel.Code K
forgetStable _ = proj₁

reflectBox
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → GradedKernel.Code K → StableCode K
reflectBox K γ = (Box K γ , box-stable K γ)

reflectBox-mono
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → ∀ {γ δ}
  → Core.Code≤ (GradedKernel.shape K) γ δ
  → StableCode≤ K (reflectBox K γ) (reflectBox K δ)
reflectBox-mono K le = box-mono K le

reflectBox-unit
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (γ : GradedKernel.Code K)
  → Core.Code≤ (GradedKernel.shape K) γ (forgetStable K (reflectBox K γ))
reflectBox-unit K γ = box-infl K γ

reflectBox-least
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    {γ : GradedKernel.Code K}
    (δ : StableCode K)
  → Core.Code≤ (GradedKernel.shape K) γ (forgetStable K δ)
  → Core.Code≤ (GradedKernel.shape K) (forgetStable K (reflectBox K γ)) (forgetStable K δ)
reflectBox-least K {γ} δ γ≤δ =
  let
    CP = Core.CodePreorder (GradedKernel.shape K)
    boxδ≤δ = ≈CP⇐ {CP = CP} (proj₂ δ)
  in
  ConPreorder.trans CP (box-mono K γ≤δ) boxδ≤δ

γ*-box-fixed
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → Core.Code≤ (GradedKernel.shape K) (GradedKernel.γ* K) (Box K (GradedKernel.γ* K))
    ×
    Core.Code≤ (GradedKernel.shape K) (Box K (GradedKernel.γ* K)) (GradedKernel.γ* K)
γ*-box-fixed K
  rewrite decode-Box K (GradedKernel.γ* K) | GradedKernel.decode-γ* K
  = GradedClosure.Th*-fixed (GradedKernel.GTruth K)

boxAt-mono-grade
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    {g g' : QAdapter.Scale Q}
  → QAdapter._≤s_ Q g g'
  → (γ : GradedKernel.Code K)
  → Core.Code≤ (GradedKernel.shape K) (BoxAt K g γ) (BoxAt K g' γ)
boxAt-mono-grade {Q = Q} K {g} {g'} g≤g' γ
  rewrite decode-BoxAt K g γ | decode-BoxAt K g' γ
  = GradedClosure.mono-grade (GradedKernel.GTruth K) g≤g' (GradedKernel.decode K γ)

-- Convenience: any bounded stabilization is below saturation.

boxAt≤Box
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (g : QAdapter.Scale Q)
    (γ : GradedKernel.Code K)
  → Core.Code≤ (GradedKernel.shape K) (BoxAt K g γ) (Box K γ)
boxAt≤Box {Q = Q} K g γ =
  boxAt-mono-grade K (GradedClosure.sat-top (GradedKernel.GTruth K) g) γ

-- Convenience: monotonicity along finite joins on the scale.

boxAt≤⊔s₁
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (g g' : QAdapter.Scale Q)
    (γ : GradedKernel.Code K)
  → Core.Code≤ (GradedKernel.shape K) (BoxAt K g γ) (BoxAt K (QAdapter._⊔s_ Q g g') γ)
boxAt≤⊔s₁ {Q = Q} K g g' γ =
  boxAt-mono-grade K (QAdapter.⊔s-ub₁ Q g g') γ

boxAt≤⊔s₂
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (g g' : QAdapter.Scale Q)
    (γ : GradedKernel.Code K)
  → Core.Code≤ (GradedKernel.shape K) (BoxAt K g' γ) (BoxAt K (QAdapter._⊔s_ Q g g') γ)
boxAt≤⊔s₂ {Q = Q} K g g' γ =
  boxAt-mono-grade K (QAdapter.⊔s-ub₂ Q g g') γ

-- --------------------------------------------------------------------------
-- BoxAt as a lax “resource action” on code
-- --------------------------------------------------------------------------

record BoxAtAction
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  : Set (lsuc ℓ) where
  field
    act
      : QAdapter.Scale Q
      → GradedKernel.Code K
      → GradedKernel.Code K

    mono
      : ∀ g {γ δ}
      → Core.Code≤ (GradedKernel.shape K) γ δ
      → Core.Code≤ (GradedKernel.shape K) (act g γ) (act g δ)

    mono-grade
      : ∀ {g g'}
      → QAdapter._≤s_ Q g g'
      → (γ : GradedKernel.Code K)
      → Core.Code≤ (GradedKernel.shape K) (act g γ) (act g' γ)

    comp-lax
      : ∀ g g' (γ : GradedKernel.Code K)
      → Core.Code≤ (GradedKernel.shape K)
          (act g' (act g γ))
          (act (QAdapter._·_ Q g g') γ)

    le-Box
      : ∀ g (γ : GradedKernel.Code K)
      → Core.Code≤ (GradedKernel.shape K) (act g γ) (Box K γ)

    le-⊔s₁
      : ∀ g g' (γ : GradedKernel.Code K)
      → Core.Code≤ (GradedKernel.shape K)
          (act g γ)
          (act (QAdapter._⊔s_ Q g g') γ)

    le-⊔s₂
      : ∀ g g' (γ : GradedKernel.Code K)
      → Core.Code≤ (GradedKernel.shape K)
          (act g' γ)
          (act (QAdapter._⊔s_ Q g g') γ)

boxAtAction
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → BoxAtAction K
boxAtAction {Q = Q} K =
  record
    { act       = BoxAt K
    ; mono      = λ g le → boxAt-mono K g le
    ; mono-grade = λ g≤g' γ → boxAt-mono-grade K g≤g' γ
    ; comp-lax  = boxAt-comp-lax K
    ; le-Box    = boxAt≤Box K
    ; le-⊔s₁    = boxAt≤⊔s₁ K
    ; le-⊔s₂    = boxAt≤⊔s₂ K
    }
