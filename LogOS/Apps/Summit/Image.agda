{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.Summit.Image where

-- Local/shared-boundary forcing on the recognised mechanisable image.
--
-- This file isolates the image-level part of the summit story: once a
-- downstream logic carries a recognised mechanisable fragment together with
-- image-local admissibility, complete presentations over the recognised shared
-- boundary contract to the canonical center.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con)
open import LogOS.LT.Presentation using (Presentation)
open import LogOS.LT.Thin2Cat using (Thin2Cat)

open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Bicategory using
  ( BicatW
  ; BicatW→TwoCellOps
  )
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.TwoCellOps using
  ( TwoCellOps )
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ShadowByView using
  ( ShadowByView )
import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.FoundationalLogic as FoundationalLogic
import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ObservationReflection.Core as ObservationReflection
import LogOS.LT.Theorems.Centering as Centering

open import LogOS.Apps.Summit.Recognition using
  ( MechanisableFragment
  ; recognisedPresentationFiber
  ; recognisedPresentationInvariance
  ; recognisedPresentationNoFork
  )
open import LogOS.Apps.Summit.Admissibility using (ObservationalSufficiency)

record SymmetryRespectingMechanisableImage
  {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
  {B : BicatW ℓObj ℓHom₁ ℓHom₂}
  {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
     → TwoCellOps.Obj (BicatW→TwoCellOps B)
     → ConPreorder ℓOCon ℓORel}
  {S : ShadowByView (BicatW→TwoCellOps B) O}
  {ℓDObj ℓDHom₁ ℓDHom₂ : Level}
  (D : Thin2Cat ℓDObj ℓDHom₁ ℓDHom₂)
  (ℓA : Level)
  : Setω where
  field
    fragment : MechanisableFragment {B = B} {O = O} {S = S} D
    admissibility : ObservationalSufficiency fragment ℓA

  presentationFiber
    : Centering.ContractibleFiber
        (ObservationReflection.CompleteBoundaryPresentationPackage S)
        ObservationReflection.CompleteBoundaryPresentationPackage≈
  presentationFiber =
    recognisedPresentationFiber fragment

  presentationNoFork
    : Centering.NoSemanticFork
        ObservationReflection.CompleteBoundaryPresentationPackage≈
  presentationNoFork =
    recognisedPresentationNoFork fragment

symmetryRespecting→noForkOnImage
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
      {B : BicatW ℓObj ℓHom₁ ℓHom₂}
      {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
         → TwoCellOps.Obj (BicatW→TwoCellOps B)
         → ConPreorder ℓOCon ℓORel}
      {S : ShadowByView (BicatW→TwoCellOps B) O}
      {ℓDObj ℓDHom₁ ℓDHom₂ : Level}
      {D : Thin2Cat ℓDObj ℓDHom₁ ℓDHom₂}
      {ℓA : Level}
  → (SR : SymmetryRespectingMechanisableImage {B = B} {O = O} {S = S} D ℓA)
  → (P : ObservationReflection.BoundaryPresentation S)
  → (Q : ObservationReflection.BoundaryPresentation S)
  → (CP : ObservationReflection.CompleteBoundaryPresentation P)
  → (CQ : ObservationReflection.CompleteBoundaryPresentation Q)
  → ∀ {A₀ B₀ : TwoCellOps.Obj (BicatW→TwoCellOps B)}
      {f g : Con (Thin2Cat.Hom (FoundationalLogic.MechanisableLogicWorld.boundaryWorld
                  (MechanisableFragment.seed
                    (SymmetryRespectingMechanisableImage.fragment SR)))
                  A₀
                  B₀)}
  → ObservationalSufficiency.VisibleRefinementOnImage
      (SymmetryRespectingMechanisableImage.admissibility SR)
      f
      g
  → Presentation._≼_ (ObservationReflection.presentationAt P {A₀} {B₀}) f g
    ×
    Presentation._≼_ (ObservationReflection.presentationAt Q {A₀} {B₀}) f g
symmetryRespecting→noForkOnImage SR P Q CP CQ visible =
  let
    module Adm = ObservationalSufficiency
      (SymmetryRespectingMechanisableImage.admissibility SR)
  in
  ( Adm.sharedBoundaryCollapse→presentedCollapse P CP visible
  , Adm.sharedBoundaryCollapse→presentedCollapse Q CQ visible
  )

symmetryRespecting→weakTerminalOnImage
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
      {B : BicatW ℓObj ℓHom₁ ℓHom₂}
      {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
         → TwoCellOps.Obj (BicatW→TwoCellOps B)
         → ConPreorder ℓOCon ℓORel}
      {S : ShadowByView (BicatW→TwoCellOps B) O}
      {ℓDObj ℓDHom₁ ℓDHom₂ : Level}
      {D : Thin2Cat ℓDObj ℓDHom₁ ℓDHom₂}
      {ℓA : Level}
  → (SR : SymmetryRespectingMechanisableImage {B = B} {O = O} {S = S} D ℓA)
  → (P : ObservationReflection.BoundaryPresentation S)
  → (CP : ObservationReflection.CompleteBoundaryPresentation P)
  → ObservationReflection.CompleteBoundaryPresentationPackage≈
      (P , CP)
      (ObservationReflection.canonicalCompleteBoundaryPresentationPackage S)
symmetryRespecting→weakTerminalOnImage SR P CP =
  recognisedPresentationInvariance
    (SymmetryRespectingMechanisableImage.fragment SR)
    P
    (ObservationReflection.canonicalBoundaryPresentation _)
    CP
    (ObservationReflection.canonicalCompleteBoundaryPresentation _)
