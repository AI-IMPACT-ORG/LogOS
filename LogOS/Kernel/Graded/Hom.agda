{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Graded.Hom where

open import LogOS.Prelude

open import LogOS.Kernel.Graded
open import LogOS.Kernel.Shape as KCore hiding (FlowCode)
open import LogOS.Kernel.HomCore as HomCore
open import LogOS.Kernel.Graded.ConAlgOf public using (conAlgOf)
open import LogOS.Kernel.Graded.HomWithGradeKit as WGKit
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.ConAlg
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

-- Optional strengthening: graded Flow preservation + transport of `Th*`.

record GradedKernelHomFlowStable {ℓ : Level}
                                 {Sig : LogOSSignature ℓ}
                                 {Q : QAdapter ℓ}
                                 (K₁ K₂ : GradedKernel Sig Q)
                                 (h : GradedKernelHom K₁ K₂)
                                 : Set (lsuc (lsuc ℓ)) where
  open GradedKernel K₁ renaming (BB to BB₁; GTruth to G₁)
  open GradedKernel K₂ renaming (BB to BB₂; GTruth to G₂)
  open GradedKernelHom h
  field
    stable-hom : GT.GradedFlowHomStable
                 (BulkBoundary.bnd BB₁)
                 (BulkBoundary.bnd BB₂)
                 G₁ G₂
                 (ConAlgHom≡.map∂ con-hom)
    step≤      : QAdapter._≤s_ Q (GradedKernel.step-grade K₁) (GradedKernel.step-grade K₂)

  open GT.GradedFlowHomStable stable-hom public

gradedKernelHomFlowOfStable
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K₁ K₂ : GradedKernel Sig Q}
    {h : GradedKernelHom K₁ K₂}
  → GradedKernelHomFlowStable K₁ K₂ h
  → GradedKernelHomFlow K₁ K₂ h
gradedKernelHomFlowOfStable {h = h} hf =
  let open GradedKernelHomFlowStable hf in
  record
    { flow-hom = GT.GradedFlowHomStable.flow-hom stable-hom
    ; step≤    = step≤
    }

-- Decode-level transport for Guard/FlowCode under Flow-preserving homs (lax).

map-guard-decode≤
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K₁ K₂ : GradedKernel Sig Q}
    {h : GradedKernelHom K₁ K₂}
    (hf : GradedKernelHomFlow K₁ K₂ h)
    (γ : GradedKernel.Code K₁)
  → ConPreorder._⊑_ (BulkBoundary.bnd (GradedKernel.BB K₂))
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
      step-pres : ConPreorder._⊑_ CP₂
                  (map∂ (Flow₁ step₁ (GradedKernel.decode K₁ γ)))
                  (Flow₂ step₁ (map∂ (GradedKernel.decode K₁ γ)))
      step-pres = preserves-F step₁ (GradedKernel.decode K₁ γ)
      step-grade : ConPreorder._⊑_ CP₂
                   (Flow₂ step₁ (map∂ (GradedKernel.decode K₁ γ)))
                   (Flow₂ step₂ (map∂ (GradedKernel.decode K₁ γ)))
      step-grade = GradedClosure.mono-grade (GradedKernel.GTruth K₂)
                    (GradedKernelHomFlow.step≤ hf)
                    (map∂ (GradedKernel.decode K₁ γ))
      step : ConPreorder._⊑_ CP₂
             (map∂ (Flow₁ step₁ (GradedKernel.decode K₁ γ)))
             (Flow₂ step₂ (map∂ (GradedKernel.decode K₁ γ)))
      step = ConPreorder.trans CP₂ step-pres step-grade
  in subst
       (λ x → ConPreorder._⊑_ CP₂ x (Flow₂ step₂ (GradedKernel.decode K₂ (mapCode γ))))
       (sym eqL)
       (subst
          (λ y → ConPreorder._⊑_ CP₂
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
  → ConPreorder._⊑_ (BulkBoundary.bnd (GradedKernel.BB K₂))
      (GradedKernel.decode K₂ (GradedKernelHom.mapCode h (FlowCode K₁ γ)))
      (GradedClosure.Flow (GradedKernel.GTruth K₂) (GradedKernel.step-grade K₂)
        (GradedKernel.decode K₂ (GradedKernelHom.mapCode h (GradedKernel.Body K₁ γ))))
map-flowcode-decode≤ {K₁ = K₁} {K₂ = K₂} {h = h} hf γ =
  map-guard-decode≤ {K₁ = K₁} {K₂ = K₂} {h = h} hf (GradedKernel.Body K₁ γ)

-- Naturality for the stable modalities on code --------------------------------

map-boxAt-decode≤
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K₁ K₂ : GradedKernel Sig Q}
    {h : GradedKernelHom K₁ K₂}
    (hf : GradedKernelHomFlow K₁ K₂ h)
    (g  : QAdapter.Scale Q)
    (γ  : GradedKernel.Code K₁)
  → ConPreorder._⊑_ (BulkBoundary.bnd (GradedKernel.BB K₂))
      (GradedKernel.decode K₂ (GradedKernelHom.mapCode h (BoxAt K₁ g γ)))
      (GradedClosure.Flow (GradedKernel.GTruth K₂) g
        (GradedKernel.decode K₂ (GradedKernelHom.mapCode h γ)))
map-boxAt-decode≤ {K₁ = K₁} {K₂ = K₂} {h = h} hf g γ =
  let
    open GradedKernelHom h
    open GT.GradedFlowHom (GradedKernelHomFlow.flow-hom hf) using (preserves-F)

    CP₂ = BulkBoundary.bnd (GradedKernel.BB K₂)
    Flow₁ = GradedClosure.Flow (GradedKernel.GTruth K₁)
    Flow₂ = GradedClosure.Flow (GradedKernel.GTruth K₂)
    map∂  = ConAlgHom≡.map∂ con-hom

    eqL : GradedKernel.decode K₂ (mapCode (BoxAt K₁ g γ))
          ≡ map∂ (Flow₁ g (GradedKernel.decode K₁ γ))
    eqL = trans (map-decode (BoxAt K₁ g γ))
                (cong map∂ (decode-BoxAt K₁ g γ))

    eqR : GradedKernel.decode K₂ (mapCode γ)
          ≡ map∂ (GradedKernel.decode K₁ γ)
    eqR = map-decode γ

    step : ConPreorder._⊑_ CP₂
             (map∂ (Flow₁ g (GradedKernel.decode K₁ γ)))
             (Flow₂ g (GradedKernel.decode K₂ (mapCode γ)))
    step =
      subst
        (λ y →
          ConPreorder._⊑_ CP₂
            (map∂ (Flow₁ g (GradedKernel.decode K₁ γ)))
            (Flow₂ g y))
        (sym eqR)
        (preserves-F g (GradedKernel.decode K₁ γ))
  in
  subst
    (λ x → ConPreorder._⊑_ CP₂ x (Flow₂ g (GradedKernel.decode K₂ (mapCode γ))))
    (sym eqL)
    step

map-boxAt≤
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K₁ K₂ : GradedKernel Sig Q}
    {h : GradedKernelHom K₁ K₂}
    (hf : GradedKernelHomFlow K₁ K₂ h)
    (g  : QAdapter.Scale Q)
    (γ  : GradedKernel.Code K₁)
  → KCore.Code≤ (GradedKernel.shape K₂)
      (GradedKernelHom.mapCode h (BoxAt K₁ g γ))
      (BoxAt K₂ g (GradedKernelHom.mapCode h γ))
map-boxAt≤ {K₂ = K₂} {h = h} hf g γ
  rewrite decode-BoxAt K₂ g (GradedKernelHom.mapCode h γ)
  = map-boxAt-decode≤ hf g γ

map-box-decode≤
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K₁ K₂ : GradedKernel Sig Q}
    {h : GradedKernelHom K₁ K₂}
    (hf : GradedKernelHomFlow K₁ K₂ h)
    (γ  : GradedKernel.Code K₁)
  → ConPreorder._⊑_ (BulkBoundary.bnd (GradedKernel.BB K₂))
      (GradedKernel.decode K₂ (GradedKernelHom.mapCode h (Box K₁ γ)))
      (GradedKernel.decode K₂ (Box K₂ (GradedKernelHom.mapCode h γ)))
map-box-decode≤ {K₁ = K₁} {K₂ = K₂} {h = h} hf γ =
  let
    CP₂ = BulkBoundary.bnd (GradedKernel.BB K₂)

    sat₁ = GradedClosure.sat (GradedKernel.GTruth K₁)

    le₁ : ConPreorder._⊑_ CP₂
            (GradedKernel.decode K₂ (GradedKernelHom.mapCode h (BoxAt K₁ sat₁ γ)))
            (GradedClosure.Flow (GradedKernel.GTruth K₂) sat₁
              (GradedKernel.decode K₂ (GradedKernelHom.mapCode h γ)))
    le₁ = map-boxAt-decode≤ {K₁ = K₁} {K₂ = K₂} {h = h} hf sat₁ γ

    le₂ : ConPreorder._⊑_ CP₂
            (GradedClosure.Flow (GradedKernel.GTruth K₂) sat₁
              (GradedKernel.decode K₂ (GradedKernelHom.mapCode h γ)))
            (GradedClosure.Flow (GradedKernel.GTruth K₂)
              (GradedClosure.sat (GradedKernel.GTruth K₂))
              (GradedKernel.decode K₂ (GradedKernelHom.mapCode h γ)))
    le₂ =
      GradedClosure.mono-grade (GradedKernel.GTruth K₂)
        (GradedClosure.sat-top (GradedKernel.GTruth K₂) sat₁)
        (GradedKernel.decode K₂ (GradedKernelHom.mapCode h γ))
  in
  subst
    (λ x →
      ConPreorder._⊑_ CP₂
        (GradedKernel.decode K₂ (GradedKernelHom.mapCode h (Box K₁ γ)))
        x)
    (sym (decode-Box K₂ (GradedKernelHom.mapCode h γ)))
    (ConPreorder.trans CP₂ le₁ le₂)

map-box≤
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K₁ K₂ : GradedKernel Sig Q}
    {h : GradedKernelHom K₁ K₂}
    (hf : GradedKernelHomFlow K₁ K₂ h)
    (γ  : GradedKernel.Code K₁)
  → KCore.Code≤ (GradedKernel.shape K₂)
      (GradedKernelHom.mapCode h (Box K₁ γ))
      (Box K₂ (GradedKernelHom.mapCode h γ))
map-box≤ hf γ = map-box-decode≤ hf γ

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
    CP₁ : ConPreorder ℓ
    CP₁ = BulkBoundary.bnd (GradedKernel.BB K₁)

    CP₂ : ConPreorder ℓ
    CP₂ = BulkBoundary.bnd (GradedKernel.BB K₂)

    Flow₁ : QAdapter.Scale Q₁ → ConPreorder.Con CP₁ → ConPreorder.Con CP₁
    Flow₁ = GradedClosure.Flow (GradedKernel.GTruth K₁)

    Flow₂ : QAdapter.Scale Q₂ → ConPreorder.Con CP₂ → ConPreorder.Con CP₂
    Flow₂ = GradedClosure.Flow (GradedKernel.GTruth K₂)

  record AccBridgeFwd {ℓA₁ ℓA₂}
                      (Acc₁ : ConPreorder.Con CP₁ → Set ℓA₁)
                      (Acc₂ : ConPreorder.Con CP₂ → Set ℓA₂)
                      : Set (lsuc (ℓ ⊔ ℓA₁ ⊔ ℓA₂)) where
    field
      acc-map  : ∀ {c} → Acc₁ c → Acc₂ (ConAlgHom≡.map∂ con-hom c)
      acc-mono : ∀ {c d} → ConPreorder._⊑_ CP₂ c d → Acc₂ c → Acc₂ d

  record AccBridgeBwd {ℓA₁ ℓA₂}
                      (Acc₁ : ConPreorder.Con CP₁ → Set ℓA₁)
                      (Acc₂ : ConPreorder.Con CP₂ → Set ℓA₂)
                      : Set (lsuc (ℓ ⊔ ℓA₁ ⊔ ℓA₂)) where
    field
      fwd         : AccBridgeFwd Acc₁ Acc₂
      acc-reflect : ∀ {c} → Acc₂ (ConAlgHom≡.map∂ con-hom c) → Acc₁ c
      flow-reflect
        : ∀ g c →
          ConPreorder._⊑_ CP₂
            (Flow₂ (grade-map g) (ConAlgHom≡.map∂ con-hom c))
            (ConAlgHom≡.map∂ con-hom (Flow₁ g c))
    open AccBridgeFwd fwd public

  mapFlowAccAt
    : ∀ {ℓA₁ ℓA₂}
      {Acc₁ : ConPreorder.Con CP₁ → Set ℓA₁}
      {Acc₂ : ConPreorder.Con CP₂ → Set ℓA₂}
      (AB : AccBridgeFwd Acc₁ Acc₂)
      → ∀ g c
      → Acc₁ (Flow₁ g c)
      → Acc₂ (Flow₂ (grade-map g) (ConAlgHom≡.map∂ con-hom c))
  mapFlowAccAt AB g c acc =
    let open AccBridgeFwd AB in
    acc-mono (FlowHom.preserves-F g c) (acc-map acc)

  mapFlowAccAt-subst
    : ∀ {ℓA₁ ℓA₂}
      {Acc₁ : ConPreorder.Con CP₁ → Set ℓA₁}
      {Acc₂ : ConPreorder.Con CP₂ → Set ℓA₂}
      (AB : AccBridgeFwd Acc₁ Acc₂)
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
      {Acc₁ : ConPreorder.Con CP₁ → Set ℓA₁}
      {Acc₂ : ConPreorder.Con CP₂ → Set ℓA₂}
      (AB : AccBridgeBwd Acc₁ Acc₂)
      → ∀ g c
      → Acc₂ (Flow₂ (grade-map g) (ConAlgHom≡.map∂ con-hom c))
      → Acc₁ (Flow₁ g c)
  mapFlowAccAt-back AB g c acc₂ =
    let open AccBridgeBwd AB in
    acc-reflect (acc-mono (flow-reflect g c) acc₂)

  mapFlowAccAt-back-subst
    : ∀ {ℓA₁ ℓA₂}
      {Acc₁ : ConPreorder.Con CP₁ → Set ℓA₁}
      {Acc₂ : ConPreorder.Con CP₂ → Set ℓA₂}
      (AB : AccBridgeBwd Acc₁ Acc₂)
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
  → ConPreorder._⊑_ (BulkBoundary.bnd (GradedKernel.BB K₂))
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
      step-pres : ConPreorder._⊑_ CP₂
                  (map∂ (Flow₁ step₁ (GradedKernel.decode K₁ γ)))
                  (Flow₂ (grade-map step₁) (map∂ (GradedKernel.decode K₁ γ)))
      step-pres = preserves-F step₁ (GradedKernel.decode K₁ γ)
      step-grade : ConPreorder._⊑_ CP₂
                   (Flow₂ (grade-map step₁) (map∂ (GradedKernel.decode K₁ γ)))
                   (Flow₂ step₂ (map∂ (GradedKernel.decode K₁ γ)))
      step-grade = GradedClosure.mono-grade (GradedKernel.GTruth K₂)
                    (GradedKernelHomFlowWithGrade.step≤ hf)
                    (map∂ (GradedKernel.decode K₁ γ))
      step : ConPreorder._⊑_ CP₂
             (map∂ (Flow₁ step₁ (GradedKernel.decode K₁ γ)))
             (Flow₂ step₂ (map∂ (GradedKernel.decode K₁ γ)))
      step = ConPreorder.trans CP₂ step-pres step-grade
  in subst
       (λ x → ConPreorder._⊑_ CP₂ x (Flow₂ step₂ (GradedKernel.decode K₂ (mapCode γ))))
       (sym eqL)
       (subst
          (λ y → ConPreorder._⊑_ CP₂
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
  → ConPreorder._⊑_ (BulkBoundary.bnd (GradedKernel.BB K₂))
      (GradedKernel.decode K₂ (GradedKernelHomWithGrade.mapCode h (FlowCode K₁ γ)))
      (GradedClosure.Flow (GradedKernel.GTruth K₂) (GradedKernel.step-grade K₂)
        (GradedKernel.decode K₂ (GradedKernelHomWithGrade.mapCode h (GradedKernel.Body K₁ γ))))
map-flowcode-decode≤-withGrade {K₁ = K₁} {K₂ = K₂} {h = h} hf γ =
  map-guard-decode≤-withGrade {K₁ = K₁} {K₂ = K₂} {h = h} hf (GradedKernel.Body K₁ γ)

map-boxAt-decode≤-withGrade
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q₁ Q₂ : QAdapter ℓ}
    {K₁ : GradedKernel Sig Q₁} {K₂ : GradedKernel Sig Q₂}
    {h : GradedKernelHomWithGrade K₁ K₂}
    (hf : GradedKernelHomFlowWithGrade K₁ K₂ h)
    (g  : QAdapter.Scale Q₁)
    (γ  : GradedKernel.Code K₁)
  → ConPreorder._⊑_ (BulkBoundary.bnd (GradedKernel.BB K₂))
      (GradedKernel.decode K₂ (GradedKernelHomWithGrade.mapCode h (BoxAt K₁ g γ)))
      (GradedClosure.Flow (GradedKernel.GTruth K₂)
        (GT.GradeHom.map (GradedKernelHomWithGrade.grade-hom h) g)
        (GradedKernel.decode K₂ (GradedKernelHomWithGrade.mapCode h γ)))
map-boxAt-decode≤-withGrade {K₁ = K₁} {K₂ = K₂} {h = h} hf g γ =
  let
    open GradedKernelHomWithGrade h
    open GT.GradedFlowHomWithGrade (GradedKernelHomFlowWithGrade.flow-hom hf) using (preserves-F)
    open GT.GradeHom grade-hom renaming (map to grade-map)

    CP₂ = BulkBoundary.bnd (GradedKernel.BB K₂)
    Flow₁ = GradedClosure.Flow (GradedKernel.GTruth K₁)
    Flow₂ = GradedClosure.Flow (GradedKernel.GTruth K₂)
    map∂  = ConAlgHom≡.map∂ con-hom

    eqL : GradedKernel.decode K₂ (mapCode (BoxAt K₁ g γ))
          ≡ map∂ (Flow₁ g (GradedKernel.decode K₁ γ))
    eqL = trans (map-decode (BoxAt K₁ g γ))
                (cong map∂ (decode-BoxAt K₁ g γ))

    eqR : GradedKernel.decode K₂ (mapCode γ)
          ≡ map∂ (GradedKernel.decode K₁ γ)
    eqR = map-decode γ

    step : ConPreorder._⊑_ CP₂
             (map∂ (Flow₁ g (GradedKernel.decode K₁ γ)))
             (Flow₂ (grade-map g) (GradedKernel.decode K₂ (mapCode γ)))
    step =
      subst
        (λ y →
          ConPreorder._⊑_ CP₂
            (map∂ (Flow₁ g (GradedKernel.decode K₁ γ)))
            (Flow₂ (grade-map g) y))
        (sym eqR)
        (preserves-F g (GradedKernel.decode K₁ γ))
  in
  subst
    (λ x → ConPreorder._⊑_ CP₂ x (Flow₂ (grade-map g) (GradedKernel.decode K₂ (mapCode γ))))
    (sym eqL)
    step

map-boxAt≤-withGrade
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q₁ Q₂ : QAdapter ℓ}
    {K₁ : GradedKernel Sig Q₁} {K₂ : GradedKernel Sig Q₂}
    {h : GradedKernelHomWithGrade K₁ K₂}
    (hf : GradedKernelHomFlowWithGrade K₁ K₂ h)
    (g  : QAdapter.Scale Q₁)
    (γ  : GradedKernel.Code K₁)
  → KCore.Code≤ (GradedKernel.shape K₂)
      (GradedKernelHomWithGrade.mapCode h (BoxAt K₁ g γ))
      (BoxAt K₂ (GT.GradeHom.map (GradedKernelHomWithGrade.grade-hom h) g)
        (GradedKernelHomWithGrade.mapCode h γ))
map-boxAt≤-withGrade {K₂ = K₂} {h = h} hf g γ
  rewrite decode-BoxAt K₂
            (GT.GradeHom.map (GradedKernelHomWithGrade.grade-hom h) g)
            (GradedKernelHomWithGrade.mapCode h γ)
  = map-boxAt-decode≤-withGrade {K₁ = _} {K₂ = K₂} {h = h} hf g γ

map-box-decode≤-withGrade
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q₁ Q₂ : QAdapter ℓ}
    {K₁ : GradedKernel Sig Q₁} {K₂ : GradedKernel Sig Q₂}
    {h : GradedKernelHomWithGrade K₁ K₂}
    (hf : GradedKernelHomFlowWithGrade K₁ K₂ h)
    (γ  : GradedKernel.Code K₁)
  → ConPreorder._⊑_ (BulkBoundary.bnd (GradedKernel.BB K₂))
      (GradedKernel.decode K₂ (GradedKernelHomWithGrade.mapCode h (Box K₁ γ)))
      (GradedKernel.decode K₂ (Box K₂ (GradedKernelHomWithGrade.mapCode h γ)))
map-box-decode≤-withGrade {K₁ = K₁} {K₂ = K₂} {h = h} hf γ =
  let
    open GradedKernelHomWithGrade h
    open GT.GradedFlowHomWithGrade (GradedKernelHomFlowWithGrade.flow-hom hf) using (sat≤)
    open GT.GradeHom grade-hom renaming (map to grade-map)

    CP₂ = BulkBoundary.bnd (GradedKernel.BB K₂)
    sat₁ = GradedClosure.sat (GradedKernel.GTruth K₁)
    sat₂ = GradedClosure.sat (GradedKernel.GTruth K₂)

    le₁ : ConPreorder._⊑_ CP₂
            (GradedKernel.decode K₂ (mapCode (BoxAt K₁ sat₁ γ)))
            (GradedClosure.Flow (GradedKernel.GTruth K₂) (grade-map sat₁)
              (GradedKernel.decode K₂ (mapCode γ)))
    le₁ = map-boxAt-decode≤-withGrade {K₁ = K₁} {K₂ = K₂} {h = h} hf sat₁ γ

    le₂ : ConPreorder._⊑_ CP₂
            (GradedClosure.Flow (GradedKernel.GTruth K₂) (grade-map sat₁)
              (GradedKernel.decode K₂ (mapCode γ)))
            (GradedClosure.Flow (GradedKernel.GTruth K₂) sat₂
              (GradedKernel.decode K₂ (mapCode γ)))
    le₂ =
      GradedClosure.mono-grade (GradedKernel.GTruth K₂) sat≤
        (GradedKernel.decode K₂ (mapCode γ))
  in
  subst
    (λ x →
      ConPreorder._⊑_ CP₂
        (GradedKernel.decode K₂ (mapCode (Box K₁ γ)))
        x)
    (sym (decode-Box K₂ (mapCode γ)))
    (ConPreorder.trans CP₂ le₁ le₂)

map-box≤-withGrade
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q₁ Q₂ : QAdapter ℓ}
    {K₁ : GradedKernel Sig Q₁} {K₂ : GradedKernel Sig Q₂}
    {h : GradedKernelHomWithGrade K₁ K₂}
    (hf : GradedKernelHomFlowWithGrade K₁ K₂ h)
    (γ  : GradedKernel.Code K₁)
  → KCore.Code≤ (GradedKernel.shape K₂)
      (GradedKernelHomWithGrade.mapCode h (Box K₁ γ))
      (Box K₂ (GradedKernelHomWithGrade.mapCode h γ))
map-box≤-withGrade hf γ = map-box-decode≤-withGrade hf γ
