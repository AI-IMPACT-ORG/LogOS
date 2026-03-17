{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.TuringCategory.ParTracked where

-- Grothendieck/Σ-totalisation for “code-tracking” partial maps
-- (refinement inherited from the base; displayed evidence ignored).
--
-- Motivation:
-- CT-like (CH2008) universality says: every partial map `f : X ⇀ Y` can be
-- simulated by running a *total* index `p : X → U` through a universal evaluator.
--
-- In LogOS, when we want morphisms/adapters to carry extra obligations or
-- witnesses, we use displayed thin 2-categories and take their Σ-totalisation
-- (category-of-elements-style; refinement inherited from the base).
--
-- This module shows that pattern for the CH2008 indexing discipline on `Par`:
--
-- - base category: the canonical partial-map model `Par`,
-- - displayed morphisms over `f` : a chosen index `p` together with totality
--   and soundness proofs,
-- - totalisation: a thin 2-category of “tracked partial maps” with a forgetful
--   functor back to `Par`.
--
-- Important scope note:
-- we use the chosen-indexer variant `TuringObjectᵇ` so that identity and
-- composition in the displayed layer can pick canonical trackers.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _≈_; ≈-refl)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Thin2Functor using (Thin2Functor)
open import LogOS.LT.DisplayedThin2Cat using
  ( DisplayedThin2Cat
  ; DecoratedThin2Cat
  ; mkTotalObjR
  ; mkTotalHomR
  ; forgetDecorated
  )

import LogOS.Apps.TuringCategory.CH2008 as CH
import LogOS.Apps.TuringCategory.PartialMaps as PM
open import LogOS.Apps.TuringCategory.ParCH2008 using (parRC; parCartesian)

module ParTrackedLocal
  {ℓCon ℓRel : Level}
  (U : ConPreorder ℓCon ℓRel)
  (TU : CH.TuringObjectᵇ (parRC {ℓCon} {ℓRel}) (parCartesian {ℓCon} {ℓRel}) U)
  where

  private
    C : Thin2Cat (lsuc (ℓCon ⊔ ℓRel)) (ℓCon ⊔ ℓRel) (ℓCon ⊔ ℓRel)
    C = PM.Par {ℓCon} {ℓRel}

  open Thin2Cat C

  -- The evaluator for this chosen Turing object.
  τ : (X Y : Obj) → Con (Hom (CH.CartesianStructure.prod (parCartesian {ℓCon} {ℓRel}) U X) Y)
  τ X Y = CH.EvalFamily.τ (CH.TuringObjectᵇ.eval TU) X Y

  -- A “tracker” for a base morphism `f : X ⇀ Y`:
  -- an index `p : X → U` plus the CH2008 totality + soundness obligations.
  TrackingLaw
    : ∀ {X Y : Obj}
    → Con (Hom X Y)
    → ⊤ {lzero}
    → ⊤ {lzero}
    → Set (ℓCon ⊔ ℓRel)
  TrackingLaw {X} {Y} f _ _ =
    Σ
      (Con (Hom X U))
      (λ p →
        CH.Total (CH.RestrictionCategory.R (parRC {ℓCon} {ℓRel})) {A = X} {B = U} p
        × _≈_
            (Hom X Y)
            (τ X Y ∘ CH.CartesianStructure.⟨_,_⟩ (parCartesian {ℓCon} {ℓRel}) p (id {A = X}))
            f)

  -- Canonical tracker chosen by the given indexer.
  track : ∀ {X Y : Obj} (f : Con (Hom X Y)) → TrackingLaw {X} {Y} f tt tt
  track f =
    CH.TuringObjectᵇ.index TU f
    , ( CH.TuringObjectᵇ.index-total TU f
      , CH.TuringObjectᵇ.index-sound TU f
      )

  TrackedDisplayed : DisplayedThin2Cat C lzero (ℓCon ⊔ ℓRel)
  TrackedDisplayed =
    record
      { Ob = λ _ → ⊤ {lzero}
      ; HomD = λ {X} {Y} (f : Con (Hom X Y)) _ _ → TrackingLaw {X} {Y} f tt tt
      ; idD = λ _ → track (id)
      ; compD = λ {f = f} {g = g} _ _ → track (g ∘ f)
      }

  ParTracked : Thin2Cat (lsuc (ℓCon ⊔ ℓRel)) (ℓCon ⊔ ℓRel) (ℓCon ⊔ ℓRel)
  ParTracked = DecoratedThin2Cat TrackedDisplayed

  -- Canonical “tracking” functor: every partial map gets decorated with its
  -- chosen index + obligations, using the `TuringObjectᵇ`-provided tracker.
  trackPar : Thin2Functor C ParTracked
  trackPar =
    let
      module S = Thin2Cat C
      module T = Thin2Cat ParTracked
    in
    record
      { mapObj = λ X → mkTotalObjR X tt
      ; mapHom = λ f → mkTotalHomR f (track f)
      ; mapHom-mono = λ le → le
      ; id-pres = λ {A} →
          ≈-refl
            (T.Hom (mkTotalObjR A tt) (mkTotalObjR A tt))
            (T.id {A = mkTotalObjR A tt})
      ; comp-pres = λ {A} {B} {C₀} f g →
          ≈-refl
            (T.Hom (mkTotalObjR A tt) (mkTotalObjR C₀ tt))
            (mkTotalHomR (f S.∘ g) (track (f S.∘ g)))
      }

  forgetParTracked : Thin2Functor ParTracked C
  forgetParTracked = forgetDecorated TrackedDisplayed

open ParTrackedLocal public using
  ( TrackingLaw
  ; track
  ; TrackedDisplayed
  ; ParTracked
  ; trackPar
  ; forgetParTracked
  )
