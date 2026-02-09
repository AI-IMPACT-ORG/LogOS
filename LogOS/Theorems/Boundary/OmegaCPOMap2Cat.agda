{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Boundary.OmegaCPOMap2Cat where

-- Thin 2-category of ωCPO maps:
-- - objects: ωCPO preorders,
-- - 1-cells: ω-continuous maps (the `OmegaCPOMap` record used by μ-fusion),
-- - 2-cells: pointwise refinement on the underlying functions (lifted).
--
-- Purpose: make the “domain-theory glue” that μ-fusion relies on available as
-- explicit 2-categorical bookkeeping, without changing any semantics.

open import LogOS.Prelude
open import LogOS.Minimal.Con using (ConPreorder; MonoMap)
open import LogOS.Minimal.RelPreorder as RP using (RelPreorder)
open import LogOS.Minimal.Truth as Truth
open import LogOS.Minimal.Thin2Cat using (Thin2Cat; Thin2CatLaws)
open import LogOS.Minimal.RelThin2Cat using (RelThin2Cat; RelThin2CatLaws)

import LogOS.Theorems.Boundary.MuFusion as MuFusion

private
  module GC = Truth.GuardedCore

module For {ℓ : Level} where

  infix 4 _⊑Ω_
  infixr 9 _∘Ω_

  record ΩObj : Set (lsuc ℓ) where
    field
      CP : ConPreorder ℓ
      ω  : GC.OmegaCPO CP

    open ConPreorder CP public using (Con; _⊑_; refl; trans)

  -- ω-continuous map between ωCPO objects (keeps the continuity witness).
  record ΩMap (A B : ΩObj) : Set (lsuc ℓ) where
    private
      module Aₛ = ΩObj A
      module Bₛ = ΩObj B
      module MF = MuFusion.For Aₛ.CP Bₛ.CP
    field
      fn   : Aₛ.Con → Bₛ.Con
      ωmap : MF.OmegaCPOMap Aₛ.ω Bₛ.ω fn

    mono : MonoMap Aₛ.CP Bₛ.CP fn
    mono = MF.OmegaCPOMap.mono-map ωmap

  -- Pointwise refinement on ωCPO maps (lifted to match the hom universe).
  _⊑Ω_ : ∀ {A B : ΩObj} → ΩMap A B → ΩMap A B → Set (lsuc ℓ)
  _⊑Ω_ {A} {B} f g =
    let
      module Bₛ = ΩObj B
    in
    Lift (lsuc ℓ) (∀ x → ConPreorder._⊑_ Bₛ.CP (ΩMap.fn f x) (ΩMap.fn g x))

  ΩMapPreorder : ΩObj → ΩObj → ConPreorder (lsuc ℓ)
  ΩMapPreorder A B =
    let
      module Bₛ = ΩObj B
    in
    record
      { Con   = ΩMap A B
      ; _⊑_   = _⊑Ω_
      ; refl  = λ {f} → lift (λ _ → ConPreorder.refl Bₛ.CP)
      ; trans = λ {f} {g} {h} fg gh →
          lift (λ x → ConPreorder.trans Bₛ.CP (Lift.lower fg x) (Lift.lower gh x))
      }

  idΩMap : ∀ {A : ΩObj} → ΩMap A A
  idΩMap {A} =
    let
      module Aₛ = ΩObj A
      module Endo = MuFusion.Endo Aₛ.CP
    in
    record
      { fn   = λ x → x
      ; ωmap = Endo.idOmegaCPOMap {ω = Aₛ.ω}
      }

  _∘Ω_ : ∀ {A B C : ΩObj} → ΩMap B C → ΩMap A B → ΩMap A C
  _∘Ω_ {A} {B} {C} g f =
    let
      module Aₛ = ΩObj A
      module Bₛ = ΩObj B
      module Cₛ = ΩObj C
      module Comp = MuFusion.Compose Aₛ.CP Bₛ.CP Cₛ.CP
    in
    record
      { fn   = λ x → ΩMap.fn g (ΩMap.fn f x)
      ; ωmap = Comp.composeOmegaCPOMap (ΩMap.ωmap f) (ΩMap.ωmap g)
      }

  -- Locally preordered 2-cat view: ωCPO maps as 1-cells, pointwise refinement as 2-cells.
  OmegaCPOThin2Cat : Thin2Cat (lsuc ℓ) (lsuc ℓ)
  OmegaCPOThin2Cat =
    record
      { Obj = ΩObj
      ; Hom = ΩMapPreorder
      ; id  = idΩMap
      ; _∘_ = _∘Ω_
      ; comp-mono-l = λ {A} {B} {C} {f} {f'} {g} le →
          lift (λ x → Lift.lower le (ΩMap.fn g x))
      ; comp-mono-r = λ {A} {B} {C} {f} {g} {g'} le →
          lift (λ x → ΩMap.mono f (Lift.lower le x))
      }

  OmegaCPOThin2CatLaws : Thin2CatLaws OmegaCPOThin2Cat
  OmegaCPOThin2CatLaws =
    record
      { id-left = λ {A} {B} f →
          let module Bₛ = ΩObj B in
          ( lift (λ _ → ConPreorder.refl Bₛ.CP)
          , lift (λ _ → ConPreorder.refl Bₛ.CP)
          )
      ; id-right = λ {A} {B} f →
          let module Bₛ = ΩObj B in
          ( lift (λ _ → ConPreorder.refl Bₛ.CP)
          , lift (λ _ → ConPreorder.refl Bₛ.CP)
          )
      ; assoc = λ {A} {B} {C} {D} f g h →
          let module Dₛ = ΩObj D in
          ( lift (λ _ → ConPreorder.refl Dₛ.CP)
          , lift (λ _ → ConPreorder.refl Dₛ.CP)
          )
      }

  -- RelPreorder-enriched version (no `Lift` needed).

  ΩMapRelPreorder : ΩObj → ΩObj → RelPreorder (lsuc ℓ) ℓ
  ΩMapRelPreorder A B =
    let
      module Bₛ = ΩObj B
    in
    record
      { Con = ΩMap A B
      ; _⊑_ = λ f g → ∀ x → ConPreorder._⊑_ Bₛ.CP (ΩMap.fn f x) (ΩMap.fn g x)
      ; refl = λ {f} _ → ConPreorder.refl Bₛ.CP
      ; trans = λ {f} {g} {h} fg gh x →
          ConPreorder.trans Bₛ.CP (fg x) (gh x)
      }

  OmegaCPORelThin2Cat : RelThin2Cat (lsuc ℓ) (lsuc ℓ) ℓ
  OmegaCPORelThin2Cat =
    record
      { Obj = ΩObj
      ; Hom = ΩMapRelPreorder
      ; id  = idΩMap
      ; _∘_ = _∘Ω_
      ; comp-mono-l = λ {A} {B} {C} {f} {f'} {g} le x →
          le (ΩMap.fn g x)
      ; comp-mono-r = λ {A} {B} {C} {f} {g} {g'} le x →
          ΩMap.mono f (le x)
      }

  OmegaCPORelThin2CatLaws : RelThin2CatLaws OmegaCPORelThin2Cat
  OmegaCPORelThin2CatLaws =
    record
      { id-left = λ {A} {B} f →
          let module Bₛ = ΩObj B in
          ((λ _ → ConPreorder.refl Bₛ.CP) , (λ _ → ConPreorder.refl Bₛ.CP))
      ; id-right = λ {A} {B} f →
          let module Bₛ = ΩObj B in
          ((λ _ → ConPreorder.refl Bₛ.CP) , (λ _ → ConPreorder.refl Bₛ.CP))
      ; assoc = λ {A} {B} {C} {D} f g h →
          let module Dₛ = ΩObj D in
          ((λ _ → ConPreorder.refl Dₛ.CP) , (λ _ → ConPreorder.refl Dₛ.CP))
      }
