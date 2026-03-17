{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.Summit.Admissibility where

-- Optional summit-side admissibility doctrine.
--
-- Formal name: `ObservationalSufficiency`.
-- Informal nickname: “No Ghost In The Machine”.
--
-- The point is to avoid the tautological slogan
--
--   “anything invisible to the recognised mechanisable image is irrelevant”
--
-- and replace it with a small list of independently meaningful guardrails for
-- an extra downstream judgement on that image:
--
-- 1. it is stated on visible downstream morphisms,
-- 2. it is invariant under visible equivalence in the downstream logic, and
-- 3. it is sound for the ambient downstream refinement relation.
--
-- Conservativity of the recognised fragment then yields the nontrivial
-- consequence: such an admissible judgement cannot backflow a new collapse into
-- the seed-visible image.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using
  ( ConPreorder
  ; Con
  ; _⊑_
  ; _≈_
  )
open import LogOS.LT.View using (idView; ExtensionalRel≈)
open import LogOS.LT.Presentation using (Presentation)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Thin2Functor using
  ( ConservativeThin2Functor
  ; mapHom-≈
  )
open import LogOS.Syntax.Prop using (from)

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

open import LogOS.Apps.Summit.Recognition using (MechanisableFragment)

record ObservationalSufficiency
  {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
  {B : BicatW ℓObj ℓHom₁ ℓHom₂}
  {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
     → TwoCellOps.Obj (BicatW→TwoCellOps B)
     → ConPreorder ℓOCon ℓORel}
  {S : ShadowByView (BicatW→TwoCellOps B) O}
  {ℓDObj ℓDHom₁ ℓDHom₂ : Level}
  {D : Thin2Cat ℓDObj ℓDHom₁ ℓDHom₂}
  (F : MechanisableFragment {B = B} {O = O} {S = S} D)
  (ℓA : Level)
  : Setω where
  private
    module Seed = FoundationalLogic.MechanisableLogicWorld
      (MechanisableFragment.seed F)
    module Boundary = Thin2Cat Seed.boundaryWorld
    module Down = Thin2Cat D
    module Gen = ConservativeThin2Functor
      (MechanisableFragment.generalisation F)

  field
    VisibleRefinement
      : ∀ {A B}
      → Con (Down.Hom (Gen.mapObj A) (Gen.mapObj B))
      → Con (Down.Hom (Gen.mapObj A) (Gen.mapObj B))
      → Set ℓA

    visibleRefinement-sound
      : ∀ {A B} {h k}
      → VisibleRefinement {A = A} {B = B} h k
      → _⊑_ (Down.Hom (Gen.mapObj A) (Gen.mapObj B)) h k

    visibleRefinement-extensional
      : ∀ {A B}
      → ExtensionalRel≈
          (idView (Down.Hom (Gen.mapObj A) (Gen.mapObj B)))
          (VisibleRefinement {A = A} {B = B})

  visibleRefinement-resp≈
    : ∀ {A B} {h h' k k'}
    → _≈_ (Down.Hom (Gen.mapObj A) (Gen.mapObj B)) h h'
    → _≈_ (Down.Hom (Gen.mapObj A) (Gen.mapObj B)) k k'
    → VisibleRefinement {A = A} {B = B} h k
    → VisibleRefinement {A = A} {B = B} h' k'
  visibleRefinement-resp≈ hh' kk' visible =
    visibleRefinement-extensional _ _ _ _ hh' kk' visible

  VisibleRefinementOnImage
    : ∀ {A B}
    → Con (Boundary.Hom A B)
    → Con (Boundary.Hom A B)
    → Set ℓA
  VisibleRefinementOnImage f g =
    VisibleRefinement (Gen.mapHom f) (Gen.mapHom g)

  visibleRefinementOnImage-resp≈
    : ∀ {A B} {f f' g g' : Con (Boundary.Hom A B)}
    → _≈_ (Boundary.Hom A B) f f'
    → _≈_ (Boundary.Hom A B) g g'
    → VisibleRefinementOnImage f g
    → VisibleRefinementOnImage f' g'
  visibleRefinementOnImage-resp≈ ff' gg' visible =
    visibleRefinement-resp≈
      (mapHom-≈ Gen.functor ff')
      (mapHom-≈ Gen.functor gg')
      visible

  noBackflow⊑
    : ∀ {A B} {f g : Con (Boundary.Hom A B)}
    → VisibleRefinementOnImage f g
    → _⊑_ (Boundary.Hom A B) f g
  noBackflow⊑ {A} {B} visible =
    Gen.reflects-hom⊑ {A = A} {B = B}
      (visibleRefinement-sound visible)

  noBackflow≈
    : ∀ {A B} {f g : Con (Boundary.Hom A B)}
    → (VisibleRefinementOnImage f g × VisibleRefinementOnImage g f)
    → _≈_ (Boundary.Hom A B) f g
  noBackflow≈ (fg , gf) =
    (noBackflow⊑ fg , noBackflow⊑ gf)

  downstreamCollapse→seedCollapse
    : ∀ {A B} {f g : Con (Boundary.Hom A B)}
    → VisibleRefinementOnImage f g
    → VisibleRefinementOnImage g f
    → _≈_ (Boundary.Hom A B) f g
  downstreamCollapse→seedCollapse fg gf =
    noBackflow≈ (fg , gf)

  sharedBoundaryCollapse→presentedCollapse
    : ∀ (P : ObservationReflection.BoundaryPresentation S)
      (CP : ObservationReflection.CompleteBoundaryPresentation P)
      {A₀ B₀ : TwoCellOps.Obj (BicatW→TwoCellOps B)}
      {f g : Con (Boundary.Hom A₀ B₀)}
    → VisibleRefinementOnImage f g
    → Presentation._≼_ (ObservationReflection.presentationAt P {A₀} {B₀}) f g
  sharedBoundaryCollapse→presentedCollapse P CP visible =
    from (Seed.presented↔boundaryKernelCanonical P CP) (noBackflow⊑ visible)

  sharedBoundaryCollapse→canonicalCollapse
    : ∀ {A₀ B₀ : TwoCellOps.Obj (BicatW→TwoCellOps B)}
      {f g : Con (Boundary.Hom A₀ B₀)}
    → VisibleRefinementOnImage f g
    → Presentation._≼_
        (ObservationReflection.presentationAt
          (ObservationReflection.canonicalBoundaryPresentation S)
          {A₀}
          {B₀})
        f g
  sharedBoundaryCollapse→canonicalCollapse =
    sharedBoundaryCollapse→presentedCollapse
      (ObservationReflection.canonicalBoundaryPresentation S)
      (ObservationReflection.canonicalCompleteBoundaryPresentation S)
