{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ObservationReflection.Core where

-- MetaTheory — Boundary semantics reflection into the LT thin-shadow world.
--
-- This module packages the positive metatheoretic claim:
-- - any boundary-sound bicategory-shaped presentation admits a canonical
--   thin approximation into the boundary-induced shadow, and
-- - any two complete homwise presentations over the same boundary semantics
--   induce mutually weakening shadows.
--
-- Upstream LT bridge:
-- each reflected hom is already a kernel `kernelFromView (μ S {A} {B})`,
-- so the boundary world is homwise internal to LT by construction.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; _⊑_)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Thin2Functor using (Thin2Functor)
open import LogOS.LT.Presentation using
  ( Presentation
  ; CompletePresentation
  ; canonicalPresentation
  ; canonicalComplete
  )
open import LogOS.LT.Presentation.Independence using (presentationsAgree)
open import LogOS.Syntax.Prop using (_↔_; to; from)
open import LogOS.LT.Kernel using
  ( Kernel
  ; kernelFromView
  ; CodePreorder
  )

open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.TwoCellOps using (TwoCellOps)
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Bicategory using
  ( BicatW
  ; BicatW→TwoCellOps
  ; BicatW→Thin2Cat
  )
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Shadow using
  ( RefinementShadow
  ; Shadow≤
  ; Shadow≤-trans
  ; ShadowHomPreorder
  ; shadowThin2Cat
  ; canonicalShadow
  ; shadowWeaken
  ; shadowApprox
  )
import LogOS.LT.Theorems.Centering as Centering
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ShadowByView using
  ( ShadowByView
  ; shadowFromView
  )
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ShadowInitiality using (ShadowForcedByView)
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.UniversalProperties using
  ( shadowApprox-asWeaken )

BoundaryWorld
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    {O : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon ℓORel}
  → ShadowByView C O
  → Thin2Cat ℓObj ℓHom₁ ℓORel
BoundaryWorld S = shadowThin2Cat (shadowFromView S)

BoundaryKernelAt
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    {O : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon ℓORel}
  → (S : ShadowByView C O)
  → ∀ {A B}
  → Kernel ℓOCon ℓORel ℓHom₁
BoundaryKernelAt S {A} {B} = kernelFromView (ShadowByView.μ S {A} {B})

BoundaryHomPreorder
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    {O : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon ℓORel}
  → (S : ShadowByView C O)
  → TwoCellOps.Obj C
  → TwoCellOps.Obj C
  → ConPreorder ℓHom₁ ℓORel
BoundaryHomPreorder S = ShadowHomPreorder (shadowFromView S)

record BoundaryPresentation
  {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
  {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
  {O : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon ℓORel}
  (S : ShadowByView C O)
  : Set (lsuc (ℓObj ⊔ ℓHom₁ ⊔ ℓHom₂ ⊔ ℓOCon ⊔ ℓORel)) where
  open TwoCellOps C using (Hom₁; _∘1_)
  field
    presentationAt
      : ∀ {A B}
      → Presentation {ℓR = ℓORel} (ShadowByView.μ S {A} {B})

    whiskerL≼
      : ∀ {A B C₀} {f f' : Hom₁ B C₀} {g : Hom₁ A B}
      → Presentation._≼_ (presentationAt {B} {C₀}) f f'
      → Presentation._≼_ (presentationAt {A} {C₀}) (f ∘1 g) (f' ∘1 g)

    whiskerR≼
      : ∀ {A B C₀} {f : Hom₁ B C₀} {g g' : Hom₁ A B}
      → Presentation._≼_ (presentationAt {A} {B}) g g'
      → Presentation._≼_ (presentationAt {A} {C₀}) (f ∘1 g) (f ∘1 g')

open BoundaryPresentation public

record CompleteBoundaryPresentation
  {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
  {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
  {O : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon ℓORel}
  {S : ShadowByView C O}
  (P : BoundaryPresentation S)
  : Set (lsuc (ℓObj ⊔ ℓHom₁ ⊔ ℓHom₂ ⊔ ℓOCon ⊔ ℓORel)) where
  field
    completeAt
      : ∀ {A B}
      → CompletePresentation (presentationAt P {A} {B})

open CompleteBoundaryPresentation public

canonicalBoundaryPresentation
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    {O : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon ℓORel}
  → (S : ShadowByView C O)
  → BoundaryPresentation S
canonicalBoundaryPresentation S =
  record
    { presentationAt = λ {A} {B} → canonicalPresentation (ShadowByView.μ S {A} {B})
    ; whiskerL≼ = ShadowByView.μ-whiskerL S
    ; whiskerR≼ = ShadowByView.μ-whiskerR S
    }

canonicalCompleteBoundaryPresentation
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    {O : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon ℓORel}
  → (S : ShadowByView C O)
  → CompleteBoundaryPresentation (canonicalBoundaryPresentation S)
canonicalCompleteBoundaryPresentation S =
  record
    { completeAt = λ {A} {B} → canonicalComplete (ShadowByView.μ S {A} {B}) }

presentationShadow
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    {O : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon ℓORel}
    {S : ShadowByView C O}
  → (P : BoundaryPresentation S)
  → CompleteBoundaryPresentation P
  → RefinementShadow {ℓRel = ℓORel} C
presentationShadow {C = C} {S = S} P CP =
  record
    { _⊑̂_ =
        λ {A} {B} f g →
          Presentation._≼_ (presentationAt P {A} {B}) f g
    ; refl̂ =
        λ {A} {B} {f} →
          Presentation.refl≼ (presentationAt P {A} {B})
    ; tranŝ =
        λ {A} {B} {f} {g} {h} fg gh →
          Presentation.trans≼ (presentationAt P {A} {B}) fg gh
    ; sound =
        λ {A} {B} {f} {g} α →
          CompletePresentation.fromCanonical
            (completeAt CP {A} {B})
            (ShadowByView.soundμ S α)
    ; whiskerL̂ =
        λ {A} {B} {C₀} {f} {f'} {g} le →
          whiskerL≼ P le
    ; whiskerR̂ =
        λ {A} {B} {C₀} {f} {g} {g'} le →
          whiskerR≼ P le
    }

BoundaryPresentationWorld
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    {O : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon ℓORel}
    {S : ShadowByView C O}
  → (P : BoundaryPresentation S)
  → CompleteBoundaryPresentation P
  → Thin2Cat ℓObj ℓHom₁ ℓORel
BoundaryPresentationWorld P CP = shadowThin2Cat (presentationShadow P CP)

presentationShadow≤boundaryShadow
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    {O : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon ℓORel}
    {S : ShadowByView C O}
    (P : BoundaryPresentation S)
    (CP : CompleteBoundaryPresentation P)
  → Shadow≤ (presentationShadow P CP) (shadowFromView S)
presentationShadow≤boundaryShadow {S = S} P CP {A} {B} {f} {g} le =
  Presentation.observe-mono (presentationAt P {A} {B}) le

boundaryShadow≤presentationShadow
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    {O : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon ℓORel}
    {S : ShadowByView C O}
    (P : BoundaryPresentation S)
    (CP : CompleteBoundaryPresentation P)
  → Shadow≤ (shadowFromView S) (presentationShadow P CP)
boundaryShadow≤presentationShadow {S = S} P CP {A} {B} {f} {g} le =
  CompletePresentation.fromCanonical
    (completeAt CP {A} {B})
    le

private
  completePresentationsAgreeAt
    : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel}
      {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
      {O : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon ℓORel}
      {S : ShadowByView C O}
      (P : BoundaryPresentation S)
      (Q : BoundaryPresentation S)
      (CP : CompleteBoundaryPresentation P)
      (CQ : CompleteBoundaryPresentation Q)
      {A B : TwoCellOps.Obj C}
      {f g : TwoCellOps.Hom₁ C A B}
    → Presentation._≼_ (presentationAt P {A} {B}) f g
      ↔ Presentation._≼_ (presentationAt Q {A} {B}) f g
  completePresentationsAgreeAt P Q CP CQ =
    presentationsAgree
      (presentationAt P)
      (presentationAt Q)
      (completeAt CP)
      (completeAt CQ)

record CompleteBoundaryPresentationsEquivalent
  {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
  {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
  {O : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon ℓORel}
  {S : ShadowByView C O}
  (P : BoundaryPresentation S)
  (Q : BoundaryPresentation S)
  (CP : CompleteBoundaryPresentation P)
  (CQ : CompleteBoundaryPresentation Q)
  : Set (lsuc (ℓObj ⊔ ℓHom₁ ⊔ ℓHom₂ ⊔ ℓOCon ⊔ ℓORel)) where

  field
    presented≤presented
      : Shadow≤ (presentationShadow P CP) (presentationShadow Q CQ)

    presented≥presented
      : Shadow≤ (presentationShadow Q CQ) (presentationShadow P CP)

    weaken₁₂
      : Thin2Functor
          (BoundaryPresentationWorld P CP)
          (BoundaryPresentationWorld Q CQ)

    weaken₂₁
      : Thin2Functor
          (BoundaryPresentationWorld Q CQ)
          (BoundaryPresentationWorld P CP)

canonicalShadow≤boundaryShadow
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel}
    {B : BicatW ℓObj ℓHom₁ ℓHom₂}
    {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
       → TwoCellOps.Obj (BicatW→TwoCellOps B)
       → ConPreorder ℓOCon ℓORel}
    (S : ShadowByView (BicatW→TwoCellOps B) O)
  → Shadow≤
      (canonicalShadow (BicatW→TwoCellOps B))
      (shadowFromView S)
canonicalShadow≤boundaryShadow {B = B} S =
  ShadowForcedByView
    S
    (canonicalShadow (BicatW→TwoCellOps B))
    (λ α → ShadowByView.soundμ S α)

bicategoryBoundaryReflection
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel}
    {B : BicatW ℓObj ℓHom₁ ℓHom₂}
    {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
       → TwoCellOps.Obj (BicatW→TwoCellOps B)
       → ConPreorder ℓOCon ℓORel}
    (S : ShadowByView (BicatW→TwoCellOps B) O)
  → Thin2Functor
      (BicatW→Thin2Cat B)
      (shadowThin2Cat (shadowFromView S))
bicategoryBoundaryReflection S = shadowApprox (shadowFromView S)

bicategoryBoundaryReflection-asWeaken
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel}
    {B : BicatW ℓObj ℓHom₁ ℓHom₂}
    {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
       → TwoCellOps.Obj (BicatW→TwoCellOps B)
       → ConPreorder ℓOCon ℓORel}
    (S : ShadowByView (BicatW→TwoCellOps B) O)
  → bicategoryBoundaryReflection {B = B} S
    ≡ shadowWeaken
        {S = canonicalShadow (BicatW→TwoCellOps B)}
        {T = shadowFromView S}
        (canonicalShadow≤boundaryShadow {B = B} S)
bicategoryBoundaryReflection-asWeaken S =
  shadowApprox-asWeaken (shadowFromView S)

completeBoundaryPresentationsEquivalentBundle
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    {O : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon ℓORel}
    {S : ShadowByView C O}
    (P : BoundaryPresentation S)
    (Q : BoundaryPresentation S)
    (CP : CompleteBoundaryPresentation P)
    (CQ : CompleteBoundaryPresentation Q)
  → CompleteBoundaryPresentationsEquivalent P Q CP CQ
completeBoundaryPresentationsEquivalentBundle P Q CP CQ =
  let
    presented≤presented : Shadow≤ (presentationShadow P CP) (presentationShadow Q CQ)
    presented≤presented {A} {B} {f} {g} le =
      to (completePresentationsAgreeAt P Q CP CQ) le

    presented≥presented : Shadow≤ (presentationShadow Q CQ) (presentationShadow P CP)
    presented≥presented {A} {B} {f} {g} le =
      from (completePresentationsAgreeAt P Q CP CQ) le
  in
  record
    { presented≤presented = presented≤presented
    ; presented≥presented = presented≥presented
    ; weaken₁₂ =
        shadowWeaken
          {S = presentationShadow P CP}
          {T = presentationShadow Q CQ}
          presented≤presented
    ; weaken₂₁ =
        shadowWeaken
          {S = presentationShadow Q CQ}
          {T = presentationShadow P CP}
          presented≥presented
    }

CompleteBoundaryPresentationPackage
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    {O : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon ℓORel}
  → (S : ShadowByView C O)
  → Set (lsuc (ℓObj ⊔ ℓHom₁ ⊔ ℓHom₂ ⊔ ℓOCon ⊔ ℓORel))
CompleteBoundaryPresentationPackage S =
  Σ
    (BoundaryPresentation S)
    (λ P → CompleteBoundaryPresentation P)

CompleteBoundaryPresentationPackage≈
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    {O : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon ℓORel}
    {S : ShadowByView C O}
  → CompleteBoundaryPresentationPackage S
  → CompleteBoundaryPresentationPackage S
  → Set (lsuc (ℓObj ⊔ ℓHom₁ ⊔ ℓHom₂ ⊔ ℓOCon ⊔ ℓORel))
CompleteBoundaryPresentationPackage≈ (P , CP) (Q , CQ) =
  CompleteBoundaryPresentationsEquivalent P Q CP CQ

completeBoundaryPresentationPackage≈-sym
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel}
      {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
      {O : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon ℓORel}
      {S : ShadowByView C O}
      {X Y : CompleteBoundaryPresentationPackage S}
  → CompleteBoundaryPresentationPackage≈ X Y
  → CompleteBoundaryPresentationPackage≈ Y X
completeBoundaryPresentationPackage≈-sym E =
  record
    { presented≤presented =
        CompleteBoundaryPresentationsEquivalent.presented≥presented E
    ; presented≥presented =
        CompleteBoundaryPresentationsEquivalent.presented≤presented E
    ; weaken₁₂ =
        CompleteBoundaryPresentationsEquivalent.weaken₂₁ E
    ; weaken₂₁ =
        CompleteBoundaryPresentationsEquivalent.weaken₁₂ E
    }

completeBoundaryPresentationPackage≈-trans
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel}
      {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
      {O : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon ℓORel}
      {S : ShadowByView C O}
      {X Y Z : CompleteBoundaryPresentationPackage S}
  → CompleteBoundaryPresentationPackage≈ X Y
  → CompleteBoundaryPresentationPackage≈ Y Z
  → CompleteBoundaryPresentationPackage≈ X Z
completeBoundaryPresentationPackage≈-trans
  {X = (P , CP)}
  {Y = (Q , CQ)}
  {Z = (R , CR)}
  E₁₂
  E₂₃ =
  let
    ≤₁₃
      : Shadow≤
          (presentationShadow P CP)
          (presentationShadow R CR)
    ≤₁₃ {A} {B} {f} {g} le =
      CompleteBoundaryPresentationsEquivalent.presented≤presented E₂₃
        (CompleteBoundaryPresentationsEquivalent.presented≤presented E₁₂ le)

    ≥₃₁
      : Shadow≤
          (presentationShadow R CR)
          (presentationShadow P CP)
    ≥₃₁ {A} {B} {f} {g} le =
      CompleteBoundaryPresentationsEquivalent.presented≥presented E₁₂
        (CompleteBoundaryPresentationsEquivalent.presented≥presented E₂₃ le)
  in
  record
    { presented≤presented = ≤₁₃
    ; presented≥presented = ≥₃₁
    ; weaken₁₂ =
        shadowWeaken
          {S = presentationShadow P CP}
          {T = presentationShadow R CR}
          ≤₁₃
    ; weaken₂₁ =
        shadowWeaken
          {S = presentationShadow R CR}
          {T = presentationShadow P CP}
          ≥₃₁
    }

canonicalCompleteBoundaryPresentationPackage
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    {O : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon ℓORel}
  → (S : ShadowByView C O)
  → CompleteBoundaryPresentationPackage S
canonicalCompleteBoundaryPresentationPackage S =
  ( canonicalBoundaryPresentation S
  , canonicalCompleteBoundaryPresentation S
  )

completeBoundaryPresentationFiber
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    {O : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon ℓORel}
  → (S : ShadowByView C O)
  → Centering.ContractibleFiber
      (CompleteBoundaryPresentationPackage S)
      CompleteBoundaryPresentationPackage≈
completeBoundaryPresentationFiber S =
  Centering.mkContractibleFiber
    completeBoundaryPresentationPackage≈-sym
    completeBoundaryPresentationPackage≈-trans
    (canonicalCompleteBoundaryPresentationPackage S)
    (λ where
      (P , CP) →
        completeBoundaryPresentationsEquivalentBundle
          P
          (canonicalBoundaryPresentation S)
          CP
          (canonicalCompleteBoundaryPresentation S))

completeBoundaryPresentationNoFork
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    {O : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon ℓORel}
  → (S : ShadowByView C O)
  → Centering.NoSemanticFork CompleteBoundaryPresentationPackage≈
completeBoundaryPresentationNoFork S =
  Centering.contractible⇒noSemanticFork
    (completeBoundaryPresentationFiber S)

completePresentation↔boundaryKernelCanonical
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    {O : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon ℓORel}
    {S : ShadowByView C O}
    (P : BoundaryPresentation S)
    (CP : CompleteBoundaryPresentation P)
    {A B : TwoCellOps.Obj C}
    {f g : TwoCellOps.Hom₁ C A B}
  → Presentation._≼_ (presentationAt P {A} {B}) f g
    ↔ _⊑_ (CodePreorder (BoundaryKernelAt S {A} {B})) f g
completePresentation↔boundaryKernelCanonical {S = S} P CP {A} {B} =
  LogOS.LT.Presentation.presentation↔canonical
    (presentationAt P {A} {B})
    (completeAt CP {A} {B})

record BoundarySemanticsTheorem
  {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
  (B : BicatW ℓObj ℓHom₁ ℓHom₂)
  (O : TwoCellOps.Obj (BicatW→TwoCellOps B)
     → TwoCellOps.Obj (BicatW→TwoCellOps B)
     → ConPreorder ℓOCon ℓORel)
  (S : ShadowByView (BicatW→TwoCellOps B) O)
  : Set (lsuc (ℓObj ⊔ ℓHom₁ ⊔ ℓHom₂ ⊔ ℓOCon ⊔ ℓORel)) where

  field
    reflection
      : Thin2Functor
          (BicatW→Thin2Cat B)
          (BoundaryWorld S)

    canonical≤boundary
      : Shadow≤
          (canonicalShadow (BicatW→TwoCellOps B))
          (shadowFromView S)

  boundaryWorld
    : Thin2Cat ℓObj ℓHom₁ ℓORel
  boundaryWorld = BoundaryWorld S

  boundaryKernelAt
    : ∀ {A₀ B₀}
    → Kernel ℓOCon ℓORel ℓHom₁
  boundaryKernelAt = BoundaryKernelAt S

  boundaryHom-isCodePreorder
    : ∀ {A₀ B₀ : TwoCellOps.Obj (BicatW→TwoCellOps B)}
    → BoundaryHomPreorder S A₀ B₀
      ≡ CodePreorder (boundaryKernelAt {A₀} {B₀})
  boundaryHom-isCodePreorder = refl

  presentedShadow
    : (P : BoundaryPresentation S)
    → CompleteBoundaryPresentation P
    → RefinementShadow {ℓRel = ℓORel} (BicatW→TwoCellOps B)
  presentedShadow = presentationShadow

  presentedShadow≤boundary
    : (P : BoundaryPresentation S)
    → (CP : CompleteBoundaryPresentation P)
    → Shadow≤ (presentedShadow P CP) (shadowFromView S)
  presentedShadow≤boundary = presentationShadow≤boundaryShadow

  boundaryPresentationWorld
    : (P : BoundaryPresentation S)
    → (CP : CompleteBoundaryPresentation P)
    → Thin2Cat ℓObj ℓHom₁ ℓORel
  boundaryPresentationWorld = BoundaryPresentationWorld

  boundary≤presentedShadow
    : (P : BoundaryPresentation S)
    → (CP : CompleteBoundaryPresentation P)
    → Shadow≤ (shadowFromView S) (presentedShadow P CP)
  boundary≤presentedShadow = boundaryShadow≤presentationShadow

  agree₁₂
    : (P : BoundaryPresentation S)
    → (Q : BoundaryPresentation S)
    → (CP : CompleteBoundaryPresentation P)
    → (CQ : CompleteBoundaryPresentation Q)
    → Shadow≤ (presentedShadow P CP) (presentedShadow Q CQ)
  agree₁₂ P Q CP CQ =
    CompleteBoundaryPresentationsEquivalent.presented≤presented
      (completeBoundaryPresentationsEquivalentBundle P Q CP CQ)

  agree₂₁
    : (P : BoundaryPresentation S)
    → (Q : BoundaryPresentation S)
    → (CP : CompleteBoundaryPresentation P)
    → (CQ : CompleteBoundaryPresentation Q)
    → Shadow≤ (presentedShadow Q CQ) (presentedShadow P CP)
  agree₂₁ P Q CP CQ =
    CompleteBoundaryPresentationsEquivalent.presented≥presented
      (completeBoundaryPresentationsEquivalentBundle P Q CP CQ)

  weaken₁₂
    : (P : BoundaryPresentation S)
    → (Q : BoundaryPresentation S)
    → (CP : CompleteBoundaryPresentation P)
    → (CQ : CompleteBoundaryPresentation Q)
    → Thin2Functor
        (shadowThin2Cat (presentedShadow P CP))
        (shadowThin2Cat (presentedShadow Q CQ))
  weaken₁₂ P Q CP CQ =
    CompleteBoundaryPresentationsEquivalent.weaken₁₂
      (completeBoundaryPresentationsEquivalentBundle P Q CP CQ)

  weaken₂₁
    : (P : BoundaryPresentation S)
    → (Q : BoundaryPresentation S)
    → (CP : CompleteBoundaryPresentation P)
    → (CQ : CompleteBoundaryPresentation Q)
    → Thin2Functor
        (boundaryPresentationWorld Q CQ)
        (boundaryPresentationWorld P CP)
  weaken₂₁ P Q CP CQ =
    CompleteBoundaryPresentationsEquivalent.weaken₂₁
      (completeBoundaryPresentationsEquivalentBundle P Q CP CQ)

  completeBoundaryPresentationsEquivalent
    : (P : BoundaryPresentation S)
    → (Q : BoundaryPresentation S)
    → (CP : CompleteBoundaryPresentation P)
    → (CQ : CompleteBoundaryPresentation Q)
    → CompleteBoundaryPresentationsEquivalent P Q CP CQ
  completeBoundaryPresentationsEquivalent = completeBoundaryPresentationsEquivalentBundle

  presented↔boundaryKernelCanonical
    : (P : BoundaryPresentation S)
    → (CP : CompleteBoundaryPresentation P)
    → ∀ {A₀ B₀ : TwoCellOps.Obj (BicatW→TwoCellOps B)}
        {f g : TwoCellOps.Hom₁ (BicatW→TwoCellOps B) A₀ B₀}
    → Presentation._≼_ (presentationAt P {A₀} {B₀}) f g
      ↔ _⊑_ (CodePreorder (boundaryKernelAt {A₀} {B₀})) f g
  presented↔boundaryKernelCanonical = completePresentation↔boundaryKernelCanonical

  reflectIntoBoundaryWorld
    : Thin2Functor
        (BicatW→Thin2Cat B)
        boundaryWorld
  reflectIntoBoundaryWorld = reflection

boundarySemanticsTheorem
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel}
    {B : BicatW ℓObj ℓHom₁ ℓHom₂}
    {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
       → TwoCellOps.Obj (BicatW→TwoCellOps B)
       → ConPreorder ℓOCon ℓORel}
    (S : ShadowByView (BicatW→TwoCellOps B) O)
  → BoundarySemanticsTheorem B O S
boundarySemanticsTheorem {B = B} S =
  record
    { reflection = bicategoryBoundaryReflection {B = B} S
    ; canonical≤boundary = canonicalShadow≤boundaryShadow {B = B} S
    }
