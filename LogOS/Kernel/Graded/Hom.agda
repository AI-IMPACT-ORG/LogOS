{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Graded.Hom where

open import LogOS.Prelude

open import LogOS.Kernel.Graded
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Algebra.ConAlg
open import LogOS.Minimal.Truth as Truth

-- Extract the constraint algebra from a graded kernel.

conAlgOf
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    → GradedKernel Sig Q → ConAlg {ℓ}
conAlgOf K = record
  { BB    = GradedKernel.BB K
  ; MBulk = GradedKernel.MBulk K
  ; MBnd  = GradedKernel.MBnd K
  ; Holo  = GradedKernel.Holo K
  }

-- Graded kernel morphism: preserves the constraint algebra (strictly) and code coherence.

record GradedKernelHom {ℓ : Level}
                       {Sig : LogOSSignature ℓ}
                       {Q : QAdapter ℓ}
                       (K₁ K₂ : GradedKernel Sig Q)
                       : Set (lsuc (lsuc ℓ)) where
  open GradedKernel K₁ renaming (BB to BB₁; MBulk to MBulk₁; MBnd to MBnd₁; Holo to Holo₁; Code to Code₁; encode to encode₁; decode to decode₁)
  open GradedKernel K₂ renaming (BB to BB₂; MBulk to MBulk₂; MBnd to MBnd₂; Holo to Holo₂; Code to Code₂; encode to encode₂; decode to decode₂)
  field
    con-hom : ConAlgHom≡ (conAlgOf K₁) (conAlgOf K₂)
    mapCode : Code₁ → Code₂
    -- Code coherence with constraints
    map-encode : ∀ c → mapCode (encode₁ c) ≡ encode₂ (ConAlgHom≡.map∂ con-hom c)
    map-decode : ∀ γ → decode₂ (mapCode γ) ≡ ConAlgHom≡.map∂ con-hom (decode₁ γ)

  -- Up-to-decode equality on code maps (helpful for quotiented initiality).
  infix 4 _≈Code_
  _≈Code_ : Code₁ → Code₁ → Set ℓ
  _≈Code_ γ δ = decode₁ γ ≡ decode₁ δ

-- Identity and composition for GradedKernelHom.

idGradedKernelHom
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q) → GradedKernelHom K K
idGradedKernelHom K = record
  { con-hom    = idHom≡ (conAlgOf K)
  ; mapCode    = λ γ → γ
  ; map-encode = λ _ → refl
  ; map-decode = λ _ → refl
  }

composeGradedKernelHom
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K₁ K₂ K₃ : GradedKernel Sig Q}
  → GradedKernelHom K₁ K₂ → GradedKernelHom K₂ K₃ → GradedKernelHom K₁ K₃
composeGradedKernelHom h₁ h₂ = record
  { con-hom    = composeHom≡ (GradedKernelHom.con-hom h₁) (GradedKernelHom.con-hom h₂)
  ; mapCode    = λ γ → GradedKernelHom.mapCode h₂ (GradedKernelHom.mapCode h₁ γ)
  ; map-encode = λ c → trans
                     (cong (GradedKernelHom.mapCode h₂) (GradedKernelHom.map-encode h₁ c))
                     (GradedKernelHom.map-encode h₂ (ConAlgHom≡.map∂ (GradedKernelHom.con-hom h₁) c))
  ; map-decode = λ γ → trans
                     (GradedKernelHom.map-decode h₂ (GradedKernelHom.mapCode h₁ γ))
                     (cong (ConAlgHom≡.map∂ (GradedKernelHom.con-hom h₂)) (GradedKernelHom.map-decode h₁ γ))
  }

-- Derived coherence for reify at decode-level under a GradedKernelHom.

map-reify-decode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K₁ K₂ : GradedKernel Sig Q}
    (h : GradedKernelHom K₁ K₂)
    (γ : GradedKernel.Code K₁)
  → GradedKernel.decode K₂ (GradedKernelHom.mapCode h (GradedKernel.reify K₁ γ))
    ≡ ConAlgHom≡.map∂ (GradedKernelHom.con-hom h) (GradedKernel.decode K₁ γ)
map-reify-decode {K₁ = K₁} {K₂ = K₂} h γ =
  let open GradedKernelHom h in
  trans (map-decode (GradedKernel.reify K₁ γ))
        (cong (ConAlgHom≡.map∂ con-hom) (GradedKernel.reify-decode K₁ γ))

-- Decode of mapped `Body`, via the boundary body `Body∂`.

map-body-decode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K₁ K₂ : GradedKernel Sig Q}
    (h : GradedKernelHom K₁ K₂)
    (γ : GradedKernel.Code K₁)
  → GradedKernel.decode K₂ (GradedKernelHom.mapCode h (GradedKernel.Body K₁ γ))
    ≡ ConAlgHom≡.map∂ (GradedKernelHom.con-hom h)
        (GradedKernel.Body∂ K₁ (GradedKernel.decode K₁ γ))
map-body-decode {K₁ = K₁} {K₂ = K₂} h γ =
  let open GradedKernelHom h in
  trans (map-decode (GradedKernel.Body K₁ γ))
        (cong (ConAlgHom≡.map∂ con-hom) (GradedKernel.body-decode K₁ γ))

-- Optional strengthening: preservation of graded Flow on boundary constraints,
-- together with step-grade alignment for guard naturality.

record GradedKernelHomFlow {ℓ : Level}
                           {Sig : LogOSSignature ℓ}
                           {Q : QAdapter ℓ}
                           (K₁ K₂ : GradedKernel Sig Q)
                           (h : GradedKernelHom K₁ K₂)
                           : Set (lsuc (lsuc ℓ)) where
  open GradedKernel K₁ renaming (BB to BB₁; GTruth to G₁)
  open GradedKernel K₂ renaming (BB to BB₂; GTruth to G₂)
  open GradedKernelHom h
  field
    flow-hom : (let module GT' = Truth.GuardedCore in GT'.GradedFlowHom)
               (BulkBoundary.bnd BB₁)
               (BulkBoundary.bnd BB₂)
               G₁ G₂
               (ConAlgHom≡.map∂ con-hom)
    step≤    : QAdapter._≤s_ Q (GradedKernel.step-grade K₁) (GradedKernel.step-grade K₂)

-- Decode-level transport for Guard/FlowCode under Flow-preserving homs (lax).

map-guard-decode≤
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K₁ K₂ : GradedKernel Sig Q}
    {h : GradedKernelHom K₁ K₂}
    (hf : GradedKernelHomFlow K₁ K₂ h)
    (γ : GradedKernel.Code K₁)
  → ConPoset._⊑_ (BulkBoundary.bnd (GradedKernel.BB K₂))
      (GradedKernel.decode K₂ (GradedKernelHom.mapCode h (GradedKernel.Guard K₁ γ)))
      (GradedClosure.Flow (GradedKernel.GTruth K₂) (GradedKernel.step-grade K₂)
        (GradedKernel.decode K₂ (GradedKernelHom.mapCode h γ)))
map-guard-decode≤ {K₁ = K₁} {K₂ = K₂} {h = h} hf γ =
  let open GradedKernelHom h
      module GT = Truth.GuardedCore
      open GT.GradedFlowHom (GradedKernelHomFlow.flow-hom hf) using (preserves-F)
      CP₂ = BulkBoundary.bnd (GradedKernel.BB K₂)
      Flow₁ = GradedClosure.Flow (GradedKernel.GTruth K₁)
      Flow₂ = GradedClosure.Flow (GradedKernel.GTruth K₂)
      step₁ = GradedKernel.step-grade K₁
      step₂ = GradedKernel.step-grade K₂
      map∂  = ConAlgHom≡.map∂ con-hom
      eqL : GradedKernel.decode K₂ (GradedKernelHom.mapCode h (GradedKernel.Guard K₁ γ))
            ≡ map∂ (Flow₁ step₁ (GradedKernel.decode K₁ γ))
      eqL = trans (map-decode (GradedKernel.Guard K₁ γ))
                  (cong map∂ (GradedKernel.guard-decode K₁ γ))
      eqR : GradedKernel.decode K₂ (GradedKernelHom.mapCode h γ)
            ≡ map∂ (GradedKernel.decode K₁ γ)
      eqR = map-decode γ
      step-pres : ConPoset._⊑_ CP₂
                  (map∂ (Flow₁ step₁ (GradedKernel.decode K₁ γ)))
                  (Flow₂ step₁ (map∂ (GradedKernel.decode K₁ γ)))
      step-pres = preserves-F step₁ (GradedKernel.decode K₁ γ)
      step-grade : ConPoset._⊑_ CP₂
                   (Flow₂ step₁ (map∂ (GradedKernel.decode K₁ γ)))
                   (Flow₂ step₂ (map∂ (GradedKernel.decode K₁ γ)))
      step-grade = GradedClosure.mono-grade (GradedKernel.GTruth K₂)
                    (GradedKernelHomFlow.step≤ hf)
                    (map∂ (GradedKernel.decode K₁ γ))
      step : ConPoset._⊑_ CP₂
             (map∂ (Flow₁ step₁ (GradedKernel.decode K₁ γ)))
             (Flow₂ step₂ (map∂ (GradedKernel.decode K₁ γ)))
      step = ConPoset.trans CP₂ step-pres step-grade
  in subst
       (λ x → ConPoset._⊑_ CP₂ x (Flow₂ step₂ (GradedKernel.decode K₂ (mapCode γ))))
       (sym eqL)
       (subst
          (λ y → ConPoset._⊑_ CP₂
                    (map∂ (Flow₁ step₁ (GradedKernel.decode K₁ γ)))
                    (Flow₂ step₂ y))
          (sym eqR)
          step)

map-flowcode-decode≤
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K₁ K₂ : GradedKernel Sig Q}
    {h : GradedKernelHom K₁ K₂}
    (hf : GradedKernelHomFlow K₁ K₂ h)
    (γ : GradedKernel.Code K₁)
  → ConPoset._⊑_ (BulkBoundary.bnd (GradedKernel.BB K₂))
      (GradedKernel.decode K₂ (GradedKernelHom.mapCode h (FlowCode K₁ γ)))
      (GradedClosure.Flow (GradedKernel.GTruth K₂) (GradedKernel.step-grade K₂)
        (GradedKernel.decode K₂ (GradedKernelHom.mapCode h (GradedKernel.Body K₁ γ))))
map-flowcode-decode≤ {K₁ = K₁} {K₂ = K₂} {h = h} hf γ =
  map-guard-decode≤ {K₁ = K₁} {K₂ = K₂} {h = h} hf (GradedKernel.Body K₁ γ)

-- Grade-reindexing homs: allow a grade morphism between different Q adapters.

record GradedKernelHomWithGrade {ℓ : Level}
                                {Sig : LogOSSignature ℓ}
                                {Q₁ Q₂ : QAdapter ℓ}
                                (K₁ : GradedKernel Sig Q₁)
                                (K₂ : GradedKernel Sig Q₂)
                                : Set (lsuc (lsuc ℓ)) where
  open GradedKernel K₁ renaming (BB to BB₁; MBulk to MBulk₁; MBnd to MBnd₁; Holo to Holo₁; Code to Code₁; encode to encode₁; decode to decode₁)
  open GradedKernel K₂ renaming (BB to BB₂; MBulk to MBulk₂; MBnd to MBnd₂; Holo to Holo₂; Code to Code₂; encode to encode₂; decode to decode₂)
  field
    con-hom   : ConAlgHom≡ (conAlgOf K₁) (conAlgOf K₂)
    mapCode   : Code₁ → Code₂
    map-encode : ∀ c → mapCode (encode₁ c) ≡ encode₂ (ConAlgHom≡.map∂ con-hom c)
    map-decode : ∀ γ → decode₂ (mapCode γ) ≡ ConAlgHom≡.map∂ con-hom (decode₁ γ)
    grade-hom : (let module GT = Truth.GuardedCore in GT.GradeHom) Q₁ Q₂

  infix 4 _≈Code_
  _≈Code_ : Code₁ → Code₁ → Set ℓ
  _≈Code_ γ δ = decode₁ γ ≡ decode₁ δ

-- Identity and composition for GradedKernelHomWithGrade.
--
-- These are the “portable” morphisms: they ignore model-specific flow
-- preservation and only transport the kernel’s structural ports (constraints,
-- code, and grade scale).

idGradedKernelHomWithGrade
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → GradedKernelHomWithGrade K K
idGradedKernelHomWithGrade K =
  record
    { con-hom   = idHom≡ (conAlgOf K)
    ; mapCode   = λ γ → γ
    ; map-encode = λ _ → refl
    ; map-decode = λ _ → refl
    ; grade-hom  = Truth.GuardedCore.idGradeHom
    }

composeGradedKernelHomWithGrade
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q₁ Q₂ Q₃ : QAdapter ℓ}
    {K₁ : GradedKernel Sig Q₁} {K₂ : GradedKernel Sig Q₂} {K₃ : GradedKernel Sig Q₃}
  → GradedKernelHomWithGrade K₁ K₂
  → GradedKernelHomWithGrade K₂ K₃
  → GradedKernelHomWithGrade K₁ K₃
composeGradedKernelHomWithGrade h₁ h₂ =
  record
    { con-hom    = composeHom≡ (GradedKernelHomWithGrade.con-hom h₁)
                               (GradedKernelHomWithGrade.con-hom h₂)
    ; mapCode    = λ γ → GradedKernelHomWithGrade.mapCode h₂
                        (GradedKernelHomWithGrade.mapCode h₁ γ)
    ; map-encode = λ c →
        trans
          (cong (GradedKernelHomWithGrade.mapCode h₂)
                (GradedKernelHomWithGrade.map-encode h₁ c))
          (GradedKernelHomWithGrade.map-encode h₂
            (ConAlgHom≡.map∂ (GradedKernelHomWithGrade.con-hom h₁) c))
    ; map-decode = λ γ →
        trans
          (GradedKernelHomWithGrade.map-decode h₂
            (GradedKernelHomWithGrade.mapCode h₁ γ))
          (cong (ConAlgHom≡.map∂ (GradedKernelHomWithGrade.con-hom h₂))
                (GradedKernelHomWithGrade.map-decode h₁ γ))
    ; grade-hom  = Truth.GuardedCore.composeGradeHom
                    (GradedKernelHomWithGrade.grade-hom h₁)
                    (GradedKernelHomWithGrade.grade-hom h₂)
    }

record GradedKernelHomFlowWithGrade {ℓ : Level}
                                    {Sig : LogOSSignature ℓ}
                                    {Q₁ Q₂ : QAdapter ℓ}
                                    (K₁ : GradedKernel Sig Q₁)
                                    (K₂ : GradedKernel Sig Q₂)
                                    (h : GradedKernelHomWithGrade K₁ K₂)
                                    : Set (lsuc (lsuc ℓ)) where
  open GradedKernel K₁ renaming (BB to BB₁; GTruth to G₁)
  open GradedKernel K₂ renaming (BB to BB₂; GTruth to G₂)
  open GradedKernelHomWithGrade h
  field
    flow-hom : (let module GT' = Truth.GuardedCore in GT'.GradedFlowHomWithGrade)
               (BulkBoundary.bnd BB₁)
               (BulkBoundary.bnd BB₂)
               G₁ G₂
               grade-hom
               (ConAlgHom≡.map∂ con-hom)
    step≤    : QAdapter._≤s_ Q₂
                 ((let module GT' = Truth.GuardedCore in GT'.GradeHom.map) grade-hom (GradedKernel.step-grade K₁))
                 (GradedKernel.step-grade K₂)

map-guard-decode≤-withGrade
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q₁ Q₂ : QAdapter ℓ}
    {K₁ : GradedKernel Sig Q₁} {K₂ : GradedKernel Sig Q₂}
    {h : GradedKernelHomWithGrade K₁ K₂}
    (hf : GradedKernelHomFlowWithGrade K₁ K₂ h)
    (γ : GradedKernel.Code K₁)
  → ConPoset._⊑_ (BulkBoundary.bnd (GradedKernel.BB K₂))
      (GradedKernel.decode K₂ (GradedKernelHomWithGrade.mapCode h (GradedKernel.Guard K₁ γ)))
      (GradedClosure.Flow (GradedKernel.GTruth K₂) (GradedKernel.step-grade K₂)
        (GradedKernel.decode K₂ (GradedKernelHomWithGrade.mapCode h γ)))
map-guard-decode≤-withGrade {K₁ = K₁} {K₂ = K₂} {h = h} hf γ =
  let open GradedKernelHomWithGrade h
      module GT = Truth.GuardedCore
      open GT.GradedFlowHomWithGrade (GradedKernelHomFlowWithGrade.flow-hom hf) using (preserves-F)
      open GT.GradeHom grade-hom renaming (map to grade-map)
      CP₂ = BulkBoundary.bnd (GradedKernel.BB K₂)
      Flow₁ = GradedClosure.Flow (GradedKernel.GTruth K₁)
      Flow₂ = GradedClosure.Flow (GradedKernel.GTruth K₂)
      step₁ = GradedKernel.step-grade K₁
      step₂ = GradedKernel.step-grade K₂
      map∂  = ConAlgHom≡.map∂ con-hom
      eqL : GradedKernel.decode K₂ (mapCode (GradedKernel.Guard K₁ γ))
            ≡ map∂ (Flow₁ step₁ (GradedKernel.decode K₁ γ))
      eqL = trans (map-decode (GradedKernel.Guard K₁ γ))
                  (cong map∂ (GradedKernel.guard-decode K₁ γ))
      eqR : GradedKernel.decode K₂ (mapCode γ)
            ≡ map∂ (GradedKernel.decode K₁ γ)
      eqR = map-decode γ
      step-pres : ConPoset._⊑_ CP₂
                  (map∂ (Flow₁ step₁ (GradedKernel.decode K₁ γ)))
                  (Flow₂ (grade-map step₁) (map∂ (GradedKernel.decode K₁ γ)))
      step-pres = preserves-F step₁ (GradedKernel.decode K₁ γ)
      step-grade : ConPoset._⊑_ CP₂
                   (Flow₂ (grade-map step₁) (map∂ (GradedKernel.decode K₁ γ)))
                   (Flow₂ step₂ (map∂ (GradedKernel.decode K₁ γ)))
      step-grade = GradedClosure.mono-grade (GradedKernel.GTruth K₂)
                    (GradedKernelHomFlowWithGrade.step≤ hf)
                    (map∂ (GradedKernel.decode K₁ γ))
      step : ConPoset._⊑_ CP₂
             (map∂ (Flow₁ step₁ (GradedKernel.decode K₁ γ)))
             (Flow₂ step₂ (map∂ (GradedKernel.decode K₁ γ)))
      step = ConPoset.trans CP₂ step-pres step-grade
  in subst
       (λ x → ConPoset._⊑_ CP₂ x (Flow₂ step₂ (GradedKernel.decode K₂ (mapCode γ))))
       (sym eqL)
       (subst
          (λ y → ConPoset._⊑_ CP₂
                    (map∂ (Flow₁ step₁ (GradedKernel.decode K₁ γ)))
                    (Flow₂ step₂ y))
          (sym eqR)
          step)

map-flowcode-decode≤-withGrade
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q₁ Q₂ : QAdapter ℓ}
    {K₁ : GradedKernel Sig Q₁} {K₂ : GradedKernel Sig Q₂}
    {h : GradedKernelHomWithGrade K₁ K₂}
    (hf : GradedKernelHomFlowWithGrade K₁ K₂ h)
    (γ : GradedKernel.Code K₁)
  → ConPoset._⊑_ (BulkBoundary.bnd (GradedKernel.BB K₂))
      (GradedKernel.decode K₂ (GradedKernelHomWithGrade.mapCode h (FlowCode K₁ γ)))
      (GradedClosure.Flow (GradedKernel.GTruth K₂) (GradedKernel.step-grade K₂)
        (GradedKernel.decode K₂ (GradedKernelHomWithGrade.mapCode h (GradedKernel.Body K₁ γ))))
map-flowcode-decode≤-withGrade {K₁ = K₁} {K₂ = K₂} {h = h} hf γ =
  map-guard-decode≤-withGrade {K₁ = K₁} {K₂ = K₂} {h = h} hf (GradedKernel.Body K₁ γ)
