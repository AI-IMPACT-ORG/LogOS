{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ObservationReflection.Laws where

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder)
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.TwoCellOps using (TwoCellOps)
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Shadow using (Shadow≤)
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ShadowByView using (ShadowByView; shadowFromView)
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ObservationReflection.Core using
  ( BoundaryPresentation
  ; CompleteBoundaryPresentation
  ; CompleteBoundaryPresentationsEquivalent
  ; boundaryShadow≤presentationShadow
  ; completeBoundaryPresentationsEquivalentBundle
  ; presentationShadow
  ; presentationShadow≤boundaryShadow
  )

boundaryPresentationSound
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    {O : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon ℓORel}
    {S : ShadowByView C O}
    (P : BoundaryPresentation S)
    (CP : CompleteBoundaryPresentation P)
  → Shadow≤ (presentationShadow P CP) (shadowFromView S)
boundaryPresentationSound = presentationShadow≤boundaryShadow

boundaryPresentationComplete
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    {O : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon ℓORel}
    {S : ShadowByView C O}
    (P : BoundaryPresentation S)
    (CP : CompleteBoundaryPresentation P)
  → Shadow≤ (shadowFromView S) (presentationShadow P CP)
boundaryPresentationComplete = boundaryShadow≤presentationShadow

boundaryPresentationShadowComparison
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    {O : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon ℓORel}
    {S : ShadowByView C O}
    (P Q : BoundaryPresentation S)
    (CP : CompleteBoundaryPresentation P)
    (CQ : CompleteBoundaryPresentation Q)
  → CompleteBoundaryPresentationsEquivalent P Q CP CQ
boundaryPresentationShadowComparison = completeBoundaryPresentationsEquivalentBundle
