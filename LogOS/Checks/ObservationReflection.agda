{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.ObservationReflection where

open import LogOS.Prelude
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Thin2Functor using (Thin2Functor)
import LogOS.LT.Theorems.Centering as Centering
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Bicategory using
  ( BicatW→TwoCellOps
  ; BicatW→Thin2Cat
  )
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Shadow using
  ( RefinementShadow
  ; Shadow≤
  ; shadowThin2Cat
  ; shadowApprox
  )
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ShadowByView using
  ( shadowFromView )
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ObservationReflection.Core using
  ( presentationShadow
  ; presentationShadow≤boundaryShadow
  ; boundaryShadow≤presentationShadow
  ; canonicalShadow≤boundaryShadow
  ; bicategoryBoundaryReflection
  ; BoundarySemanticsTheorem
  ; boundarySemanticsTheorem
  ; CompleteBoundaryPresentationPackage
  ; CompleteBoundaryPresentationPackage≈
  ; canonicalCompleteBoundaryPresentationPackage
  ; completeBoundaryPresentationFiber
  ; completeBoundaryPresentationNoFork
  )
open import LogOS.Checks.Support.TrivialBoundaryWorld using (B; O; S; P; CP)
import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ObservationReflection.Core as ObservationReflection

reflection
  : Thin2Functor
      (BicatW→Thin2Cat B)
      (shadowThin2Cat (shadowFromView S))
reflection = bicategoryBoundaryReflection {B = B} S

reflection-refl
  : bicategoryBoundaryReflection {B = B} S
    ≡ shadowApprox (shadowFromView S)
reflection-refl = refl

presented
  : RefinementShadow (BicatW→TwoCellOps B)
presented = presentationShadow P CP

presented≤boundary
  : Shadow≤ presented (shadowFromView S)
presented≤boundary {A} {B₀} {f} {g} le =
  presentationShadow≤boundaryShadow
    {ℓObj = lzero}
    {ℓHom₁ = lzero}
    {ℓHom₂ = lzero}
    {ℓOCon = lzero}
    {ℓORel = lzero}
    {C = BicatW→TwoCellOps B}
    {O = O}
    {S = S}
    P CP
    {A = A}
    {B = B₀}
    {f = f}
    {g = g}
    le

boundary≤presented
  : Shadow≤ (shadowFromView S) presented
boundary≤presented {A} {B₀} {f} {g} le =
  boundaryShadow≤presentationShadow
    {ℓObj = lzero}
    {ℓHom₁ = lzero}
    {ℓHom₂ = lzero}
    {ℓOCon = lzero}
    {ℓORel = lzero}
    {C = BicatW→TwoCellOps B}
    {O = O}
    {S = S}
    P CP
    {A = A}
    {B = B₀}
    {f = f}
    {g = g}
    le

canonical≤boundary
  : Shadow≤
      (LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Shadow.canonicalShadow
        (BicatW→TwoCellOps B))
      (shadowFromView S)
canonical≤boundary {A} {B₀} {f} {g} le =
  canonicalShadow≤boundaryShadow
    {ℓObj = lzero}
    {ℓHom₁ = lzero}
    {ℓHom₂ = lzero}
    {ℓOCon = lzero}
    {ℓORel = lzero}
    {B = B}
    {O = O}
    S
    {A = A}
    {B = B₀}
    {f = f}
    {g = g}
    le

directWeakenSelf
  : Thin2Functor
      (shadowThin2Cat presented)
      (shadowThin2Cat presented)
directWeakenSelf =
  ObservationReflection.CompleteBoundaryPresentationsEquivalent.weaken₁₂
    (ObservationReflection.completeBoundaryPresentationsEquivalentBundle P P CP CP)

theorem : BoundarySemanticsTheorem B O S
theorem = boundarySemanticsTheorem {B = B} {O = O} S

module OR = ObservationReflection.BoundarySemanticsTheorem theorem

bundleReflection
  : Thin2Functor
      (BicatW→Thin2Cat B)
      (shadowThin2Cat (shadowFromView S))
bundleReflection = OR.reflectIntoBoundaryWorld

bundledWeakenSelf
  : Thin2Functor
      (shadowThin2Cat presented)
      (shadowThin2Cat presented)
bundledWeakenSelf = OR.weaken₁₂ P P CP CP

package
  : CompleteBoundaryPresentationPackage S
package = (P , CP)

canonicalPackage
  : CompleteBoundaryPresentationPackage S
canonicalPackage = canonicalCompleteBoundaryPresentationPackage S

fiber
  : Centering.ContractibleFiber
      (CompleteBoundaryPresentationPackage S)
      CompleteBoundaryPresentationPackage≈
fiber = completeBoundaryPresentationFiber S

packageContractsToCenter
  : CompleteBoundaryPresentationPackage≈ package canonicalPackage
packageContractsToCenter =
  Centering.contract fiber package

packageNoFork
  : CompleteBoundaryPresentationPackage≈ package package
packageNoFork =
  completeBoundaryPresentationNoFork S {x = package} {y = package}
