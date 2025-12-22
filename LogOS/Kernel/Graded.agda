{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Graded where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.World
open import LogOS.Minimal.Con
open import LogOS.Minimal.Adjunction
open import LogOS.Minimal.Truth as Truth
open import LogOS.Syntax.Prop as Prop

open Truth.GuardedCore public using
  ( GradedClosure
  ; GradeHom
  ; GradedFlowHom
  ; GradedFlowHomWithGrade
  ; forgetGradedClosure
  )

-- Graded kernel: same S/H/Code layers as Kernel, but guarded flow is graded.
record GradedKernel {ℓ : Level}
                    (Sig : LogOSSignature ℓ)
                    (Q   : QAdapter ℓ)
                    : Set (lsuc (lsuc ℓ)) where
  open LogOSSignature Sig
  module W = Worlds Sig
  open Truth.StrictTruth Sig
  field
    -- H-tier: world context + Q-weighted flow
    HWorld : W.WorldH Q

  private
    module HT = Truth.HomotypicalTruth Sig Q HWorld

  field
    -- Constraints and lax monoidal adjunction
    BB     : BulkBoundary ℓ
    MBulk  : MonoidalPoset (BulkBoundary.bulk BB)
    MBnd   : MonoidalPoset (BulkBoundary.bnd  BB)
    Holo   : LaxMonoidalAdjunction BB MBulk MBnd

    -- H-tier satisfaction and invariance (dependent on the chosen world)
    HTruth : HT.HLayer BB
    HInv   : HT.Invariance BB

    -- Boundary satisfaction + coherence (optional, internalized)
    Sat_H_bnd : ∂Cosp → (ConPoset.Con (BulkBoundary.bnd BB)) → Set ℓ
    sat-coh   : ∀ (w : Cosp) (c : ConPoset.Con (BulkBoundary.bnd BB)) →
                Prop._↔_ (HT.HLayer.Sat_H HTruth w c)
                         (Sat_H_bnd (bnd w) c)

    -- S-tier: strict logic interface and translation into H-tier constraints
    Fml    : Set ℓ
    Strict : StrictLayer Fml
    TransH : Fml → (ConPoset.Con (BulkBoundary.bnd BB))
    coh-LH : ∀ (w : Cosp) (φ : Fml) →
             Prop._↔_ (StrictLayer.Sat_S Strict w φ)
                      (HT.HLayer.Sat_H HTruth w (TransH φ))

    -- G-tier: graded guarded truth closure on boundary constraints
    GTruth : GradedClosure Q (BulkBoundary.bnd BB)

    -- Code layer: guarded reflection
    Code   : Set ℓ
    encode : (ConPoset.Con (BulkBoundary.bnd BB)) → Code
    decode : Code → (ConPoset.Con (BulkBoundary.bnd BB))
    decode∘encode : ∀ c → decode (encode c) ≡ c
    Guard         : Code → Code
    Body          : Code → Code
    step-grade    : QAdapter.Scale Q
    guard-decode  : ∀ γ → decode (Guard γ) ≡ (GradedClosure.Flow GTruth step-grade) (decode γ)
    -- Guarded fixpoint (saturated grade from GTruth)
    γ*            : Code
    -- `γ*` is a code-level witness for the guarded fixed point, but we only
    -- require closure-style strength: stability under one `FlowCode` step is
    -- expressed as boundary preorder inequalities (not a definitional code
    -- equality). This avoids silently conflating step-grade Flow with
    -- saturation-grade fixed points.
    γ*-guard      : (ConPoset._⊑_ (BulkBoundary.bnd BB)
                      (decode γ*)
                      (decode (Guard (Body γ*))))
                    × (ConPoset._⊑_ (BulkBoundary.bnd BB)
                        (decode (Guard (Body γ*)))
                        (decode γ*))
    decode-γ*     : decode γ* ≡ (GradedClosure.Th* GTruth)

    -- Safe self-reflection (observational)
    reify         : Code → Code
    reify-decode  : ∀ γ → decode (reify γ) ≡ decode γ
    Body∂         : (ConPoset.Con (BulkBoundary.bnd BB)) → (ConPoset.Con (BulkBoundary.bnd BB))
    body-decode   : ∀ γ → decode (Body γ) ≡ Body∂ (decode γ)

-- Derived code-level Flow (Guard ∘ Body).
FlowCode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q) → GradedKernel.Code K → GradedKernel.Code K
FlowCode K γ = GradedKernel.Guard K (GradedKernel.Body K γ)

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
-- distinguished fixed point `Th*` lives at the saturation grade. The following
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
  → ConPoset._⊑_ (BulkBoundary.bnd (GradedKernel.BB K))
      (GradedKernel.decode K (GradedKernel.Guard K γ))
      (GradedClosure.Flow (GradedKernel.GTruth K) (GradedClosure.sat (GradedKernel.GTruth K))
        (GradedKernel.decode K γ))
guard-decode≤sat K γ =
  let open GradedKernel K
      CP = BulkBoundary.bnd BB
      le = GradedClosure.mono-grade GTruth (step≤sat K) (decode γ)
  in subst (λ x → ConPoset._⊑_ CP x (GradedClosure.Flow GTruth (GradedClosure.sat GTruth) (decode γ)))
           (sym (guard-decode γ))
           le

decode-FlowCode≤sat
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q) (γ : GradedKernel.Code K)
  → ConPoset._⊑_ (BulkBoundary.bnd (GradedKernel.BB K))
      (GradedKernel.decode K (FlowCode K γ))
      (GradedClosure.Flow (GradedKernel.GTruth K) (GradedClosure.sat (GradedKernel.GTruth K))
        (GradedKernel.Body∂ K (GradedKernel.decode K γ)))
decode-FlowCode≤sat K γ =
  let open GradedKernel K
      CP = BulkBoundary.bnd BB
      le = GradedClosure.mono-grade GTruth (step≤sat K) (Body∂ (decode γ))
  in subst (λ x → ConPoset._⊑_ CP x (GradedClosure.Flow GTruth (GradedClosure.sat GTruth) (Body∂ (decode γ))))
           (sym (decode-FlowCode K γ))
           le

record BodyMonotone
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q) : Set (lsuc (lsuc ℓ)) where
  field
    mono-Body∂
      : ∀ {c d}
      → ConPoset._⊑_ (BulkBoundary.bnd (GradedKernel.BB K)) c d
      → ConPoset._⊑_ (BulkBoundary.bnd (GradedKernel.BB K)) (GradedKernel.Body∂ K c) (GradedKernel.Body∂ K d)
