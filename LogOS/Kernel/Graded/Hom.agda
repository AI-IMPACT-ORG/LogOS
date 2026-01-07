{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Graded.Hom where

open import LogOS.Prelude

open import LogOS.Kernel.Graded
open import LogOS.Kernel.HomCore as HomCore
open import LogOS.Kernel.Graded.ConAlgOf public using (conAlgOf)
open import LogOS.Kernel.Graded.HomWithGradeKit as WGKit
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Algebra.ConAlg
open import LogOS.Minimal.Truth as Truth

private
  module GT = Truth.GuardedCore

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} where
  private
    ops : HomCore.Ops {ℓ}
    ops =
      record
        { Obj          = GradedKernel Sig Q
        ; conAlgOf     = conAlgOf
        ; Code         = GradedKernel.Code
        ; encode       = GradedKernel.encode
        ; decode       = GradedKernel.decode
        ; reify        = GradedKernel.reify
        ; reify-decode = GradedKernel.reify-decode
        ; Body         = GradedKernel.Body
        ; Body∂        = GradedKernel.Body∂
        ; body-decode  = GradedKernel.body-decode
        }

  open HomCore.WithOps ops public
    renaming
      ( Hom              to GradedKernelHom
      ; idHom            to idGradedKernelHom
      ; composeHom       to composeGradedKernelHom
      ; map-reify-decode to map-reify-decode
      ; map-body-decode  to map-body-decode
      )

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
    flow-hom : GT.GradedFlowHom
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

private
  module WithGradeCore {ℓ : Level} {Sig : LogOSSignature ℓ} = WGKit.ForSig {ℓ = ℓ} Sig

record GradedKernelHomWithGrade {ℓ : Level}
                                {Sig : LogOSSignature ℓ}
                                {Q₁ Q₂ : QAdapter ℓ}
                                (K₁ : GradedKernel Sig Q₁)
                                (K₂ : GradedKernel Sig Q₂)
                                : Set (lsuc (lsuc ℓ)) where
  private
    module WG = WithGradeCore {ℓ = ℓ} {Sig = Sig}

  field
    hom : WG.Core.HomWithGrade K₁ K₂

  open WG.Core.HomWithGrade hom public

-- Identity and composition for GradedKernelHomWithGrade.
--
-- These are the “portable” morphisms: they ignore model-specific flow
-- preservation and only transport the kernel’s structural ports (constraints,
-- code, and grade scale).

idGradedKernelHomWithGrade
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → GradedKernelHomWithGrade K K
idGradedKernelHomWithGrade {ℓ = ℓ} {Sig = Sig} K =
  record
    { hom = WG.Core.idHomWithGrade K }
  where
    module WG = WithGradeCore {ℓ = ℓ} {Sig = Sig}

composeGradedKernelHomWithGrade
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q₁ Q₂ Q₃ : QAdapter ℓ}
    {K₁ : GradedKernel Sig Q₁} {K₂ : GradedKernel Sig Q₂} {K₃ : GradedKernel Sig Q₃}
  → GradedKernelHomWithGrade K₁ K₂
  → GradedKernelHomWithGrade K₂ K₃
  → GradedKernelHomWithGrade K₁ K₃
composeGradedKernelHomWithGrade {ℓ = ℓ} {Sig = Sig} h₁ h₂ =
  record
    { hom = WG.Core.composeHomWithGrade
              (GradedKernelHomWithGrade.hom h₁)
              (GradedKernelHomWithGrade.hom h₂)
    }
  where
    module WG = WithGradeCore {ℓ = ℓ} {Sig = Sig}

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
    flow-hom : GT.GradedFlowHomWithGrade
               (BulkBoundary.bnd BB₁)
               (BulkBoundary.bnd BB₂)
               G₁ G₂
               grade-hom
               (ConAlgHom≡.map∂ con-hom)
    step≤    : QAdapter._≤s_ Q₂
                 (GT.GradeHom.map grade-hom (GradedKernel.step-grade K₁))
                 (GradedKernel.step-grade K₂)

-- --------------------------------------------------------------------------
-- Flow/acceptance transport kit (grade-reindexing).
-- --------------------------------------------------------------------------
--
-- Many application-level bridges (e.g. resource→resource transport) need a
-- small reusable lemma: if a predicate `Acc₁` on boundary constraints is mapped
-- across a boundary hom and the target predicate `Acc₂` is monotone, then
-- “within Flow g” facts transport along a Flow-preserving hom (lax).
--
-- The `flow-reflect` direction is intentionally an explicit assumption: the
-- core `GradedFlowHomWithGrade` only provides the forward inequality.

module FlowAccTransportWithGrade
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q₁ Q₂ : QAdapter ℓ}
  (K₁ : GradedKernel Sig Q₁)
  (K₂ : GradedKernel Sig Q₂)
  (h  : GradedKernelHomWithGrade K₁ K₂)
  (hf : GradedKernelHomFlowWithGrade K₁ K₂ h)
  where

  open GradedKernelHomWithGrade h
  module GH = GT.GradeHom grade-hom
  open GH renaming (map to grade-map)
  module FlowHom = GT.GradedFlowHomWithGrade (GradedKernelHomFlowWithGrade.flow-hom hf)

  private
    CP₁ : ConPoset ℓ
    CP₁ = BulkBoundary.bnd (GradedKernel.BB K₁)

    CP₂ : ConPoset ℓ
    CP₂ = BulkBoundary.bnd (GradedKernel.BB K₂)

    Flow₁ : QAdapter.Scale Q₁ → ConPoset.Con CP₁ → ConPoset.Con CP₁
    Flow₁ = GradedClosure.Flow (GradedKernel.GTruth K₁)

    Flow₂ : QAdapter.Scale Q₂ → ConPoset.Con CP₂ → ConPoset.Con CP₂
    Flow₂ = GradedClosure.Flow (GradedKernel.GTruth K₂)

  record AccBridge {ℓA₁ ℓA₂}
                   (Acc₁ : ConPoset.Con CP₁ → Set ℓA₁)
                   (Acc₂ : ConPoset.Con CP₂ → Set ℓA₂)
                   : Set (lsuc (ℓ ⊔ ℓA₁ ⊔ ℓA₂)) where
    field
      acc-map     : ∀ {c} → Acc₁ c → Acc₂ (ConAlgHom≡.map∂ con-hom c)
      acc-reflect : ∀ {c} → Acc₂ (ConAlgHom≡.map∂ con-hom c) → Acc₁ c
      acc-mono    : ∀ {c d} → ConPoset._⊑_ CP₂ c d → Acc₂ c → Acc₂ d

      flow-reflect
        : ∀ g c →
          ConPoset._⊑_ CP₂
            (Flow₂ (grade-map g) (ConAlgHom≡.map∂ con-hom c))
            (ConAlgHom≡.map∂ con-hom (Flow₁ g c))

  mapFlowAccAt
    : ∀ {ℓA₁ ℓA₂}
      {Acc₁ : ConPoset.Con CP₁ → Set ℓA₁}
      {Acc₂ : ConPoset.Con CP₂ → Set ℓA₂}
      (AB : AccBridge Acc₁ Acc₂)
      → ∀ g c
      → Acc₁ (Flow₁ g c)
      → Acc₂ (Flow₂ (grade-map g) (ConAlgHom≡.map∂ con-hom c))
  mapFlowAccAt AB g c acc =
    let open AccBridge AB in
    acc-mono (FlowHom.preserves-F g c) (acc-map acc)

  mapFlowAccAt-subst
    : ∀ {ℓA₁ ℓA₂}
      {Acc₁ : ConPoset.Con CP₁ → Set ℓA₁}
      {Acc₂ : ConPoset.Con CP₂ → Set ℓA₂}
      (AB : AccBridge Acc₁ Acc₂)
      → ∀ g c d₂
      → d₂ ≡ ConAlgHom≡.map∂ con-hom c
      → Acc₁ (Flow₁ g c)
      → Acc₂ (Flow₂ (grade-map g) d₂)
  mapFlowAccAt-subst {Acc₂ = Acc₂} AB g c d₂ eq acc =
    subst (λ d → Acc₂ (Flow₂ (grade-map g) d))
          (sym eq)
          (mapFlowAccAt AB g c acc)

  mapFlowAccAt-back
    : ∀ {ℓA₁ ℓA₂}
      {Acc₁ : ConPoset.Con CP₁ → Set ℓA₁}
      {Acc₂ : ConPoset.Con CP₂ → Set ℓA₂}
      (AB : AccBridge Acc₁ Acc₂)
      → ∀ g c
      → Acc₂ (Flow₂ (grade-map g) (ConAlgHom≡.map∂ con-hom c))
      → Acc₁ (Flow₁ g c)
  mapFlowAccAt-back AB g c acc₂ =
    let open AccBridge AB in
    acc-reflect (acc-mono (flow-reflect g c) acc₂)

  mapFlowAccAt-back-subst
    : ∀ {ℓA₁ ℓA₂}
      {Acc₁ : ConPoset.Con CP₁ → Set ℓA₁}
      {Acc₂ : ConPoset.Con CP₂ → Set ℓA₂}
      (AB : AccBridge Acc₁ Acc₂)
      → ∀ g c d₂
      → d₂ ≡ ConAlgHom≡.map∂ con-hom c
      → Acc₂ (Flow₂ (grade-map g) d₂)
      → Acc₁ (Flow₁ g c)
  mapFlowAccAt-back-subst {Acc₂ = Acc₂} AB g c d₂ eq acc₂ =
    mapFlowAccAt-back AB g c
      (subst (λ d → Acc₂ (Flow₂ (grade-map g) d)) eq acc₂)

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
