{-
  LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
  Copyright (C) 2026 AI.IMPACT GmbH
  SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ObsContext.TwoD where

-- 2D contexts (views on each hom, i.e. ShadowByView packages).
--
-- Dependent-first: the observation preorder may vary by object pair.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; _×CP_)
open import LogOS.LT.View using
  ( _⊑[_]_
  ; pairView-fst
  ; pairView-snd
  ; pairView-intro
  )

open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Thin2Functor using (Thin2Functor)

open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.TwoCellOps using (TwoCellOps)
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Shadow using
  ( RefinementShadow
  ; Shadow≤
  ; shadowThin2Cat
  ; shadowWeaken
  )
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ShadowByView using
  ( ShadowByView
  ; pairShadowByView
  ; pairShadowByView≤₁
  ; pairShadowByView≤₂
  ; pairShadowByView-glb
  ; shadowFromView
  )

record ObsContext₂
  {ℓObj ℓHom₁ ℓHom₂ : Level}
  (C : TwoCellOps ℓObj ℓHom₁ ℓHom₂)
  (ℓOCon ℓORel : Level)
  : Set (lsuc (ℓObj ⊔ ℓHom₁ ⊔ ℓHom₂ ⊔ ℓOCon ⊔ ℓORel)) where
  field
    O : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon ℓORel
    S : ShadowByView C O

infix 4 _≤Ctx₂_
_≤Ctx₂_
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon₁ ℓORel₁ ℓOCon₂ ℓORel₂}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
  → ObsContext₂ C ℓOCon₁ ℓORel₁
  → ObsContext₂ C ℓOCon₂ ℓORel₂
  → Set (ℓObj ⊔ ℓHom₁ ⊔ ℓORel₁ ⊔ ℓORel₂)
_≤Ctx₂_ {C = C} κ κ' =
  ∀ {A B} {f g : TwoCellOps.Hom₁ C A B}
  → f ⊑[ ShadowByView.μ (ObsContext₂.S κ') {A} {B} ] g
  → f ⊑[ ShadowByView.μ (ObsContext₂.S κ) {A} {B} ] g

infixl 7 _⊔Ctx₂_
_⊔Ctx₂_
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon₁ ℓORel₁ ℓOCon₂ ℓORel₂}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
  → ObsContext₂ C ℓOCon₁ ℓORel₁
  → ObsContext₂ C ℓOCon₂ ℓORel₂
  → ObsContext₂ C (ℓOCon₁ ⊔ ℓOCon₂) (ℓORel₁ ⊔ ℓORel₂)
κ ⊔Ctx₂ κ' =
  record
    { O = λ A B → ObsContext₂.O κ A B ×CP ObsContext₂.O κ' A B
    ; S = pairShadowByView (ObsContext₂.S κ) (ObsContext₂.S κ')
    }

≤Ctx₂-⊔₁
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon₁ ℓORel₁ ℓOCon₂ ℓORel₂}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    (κ : ObsContext₂ C ℓOCon₁ ℓORel₁)
    (κ' : ObsContext₂ C ℓOCon₂ ℓORel₂)
  → κ ≤Ctx₂ (κ ⊔Ctx₂ κ')
≤Ctx₂-⊔₁ κ κ' {A} {B} {f} {g} le =
  pairView-fst
    {V₁ = ShadowByView.μ (ObsContext₂.S κ) {A} {B}}
    {V₂ = ShadowByView.μ (ObsContext₂.S κ') {A} {B}}
    {x = f}
    {y = g}
    le

≤Ctx₂-⊔₂
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon₁ ℓORel₁ ℓOCon₂ ℓORel₂}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    (κ : ObsContext₂ C ℓOCon₁ ℓORel₁)
    (κ' : ObsContext₂ C ℓOCon₂ ℓORel₂)
  → κ' ≤Ctx₂ (κ ⊔Ctx₂ κ')
≤Ctx₂-⊔₂ κ κ' {A} {B} {f} {g} le =
  pairView-snd
    {V₁ = ShadowByView.μ (ObsContext₂.S κ) {A} {B}}
    {V₂ = ShadowByView.μ (ObsContext₂.S κ') {A} {B}}
    {x = f}
    {y = g}
    le

⊔Ctx₂-least
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon₁ ℓORel₁ ℓOCon₂ ℓORel₂ ℓOCon₃ ℓORel₃}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    {κ : ObsContext₂ C ℓOCon₁ ℓORel₁}
    {κ' : ObsContext₂ C ℓOCon₂ ℓORel₂}
    {E : ObsContext₂ C ℓOCon₃ ℓORel₃}
  → κ ≤Ctx₂ E
  → κ' ≤Ctx₂ E
  → (κ ⊔Ctx₂ κ') ≤Ctx₂ E
⊔Ctx₂-least {κ = κ} {κ' = κ'} κ≤E κ'≤E {A} {B} {f} {g} le =
  pairView-intro
    {V₁ = ShadowByView.μ (ObsContext₂.S κ) {A} {B}}
    {V₂ = ShadowByView.μ (ObsContext₂.S κ') {A} {B}}
    (κ≤E le)
    (κ'≤E le)

-- Thin approximation induced by a 2D context.
shadowAt
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
  → ObsContext₂ C ℓOCon ℓORel
  → RefinementShadow {ℓRel = ℓORel} C
shadowAt κ = shadowFromView (ObsContext₂.S κ)

thinAt
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
  → ObsContext₂ C ℓOCon ℓORel
  → Thin2Cat ℓObj ℓHom₁ ℓORel
thinAt κ = shadowThin2Cat (shadowAt κ)

-- Context join (add observables) corresponds to a meet/GLB on induced shadows.
--
-- Intuition:
-- - `κ ⊔Ctx₂ κ'` observes by a product view, hence refines iff both components
--   refine.
-- - In the shadow preorder `Shadow≤` (relation inclusion), this is exactly the
--   intersection/meet.

shadowAt-⊔Ctx₂≤₁
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon₁ ℓORel₁ ℓOCon₂ ℓORel₂}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    (κ : ObsContext₂ C ℓOCon₁ ℓORel₁)
    (κ' : ObsContext₂ C ℓOCon₂ ℓORel₂)
  → Shadow≤ (shadowAt (κ ⊔Ctx₂ κ')) (shadowAt κ)
shadowAt-⊔Ctx₂≤₁ κ κ' =
  pairShadowByView≤₁ (ObsContext₂.S κ) (ObsContext₂.S κ')

shadowAt-⊔Ctx₂≤₂
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon₁ ℓORel₁ ℓOCon₂ ℓORel₂}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    (κ : ObsContext₂ C ℓOCon₁ ℓORel₁)
    (κ' : ObsContext₂ C ℓOCon₂ ℓORel₂)
  → Shadow≤ (shadowAt (κ ⊔Ctx₂ κ')) (shadowAt κ')
shadowAt-⊔Ctx₂≤₂ κ κ' =
  pairShadowByView≤₂ (ObsContext₂.S κ) (ObsContext₂.S κ')

shadowAt-⊔Ctx₂-glb
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓRel ℓOCon₁ ℓORel₁ ℓOCon₂ ℓORel₂}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    {R : RefinementShadow {ℓRel = ℓRel} C}
    (κ : ObsContext₂ C ℓOCon₁ ℓORel₁)
    (κ' : ObsContext₂ C ℓOCon₂ ℓORel₂)
  → Shadow≤ R (shadowAt κ)
  → Shadow≤ R (shadowAt κ')
  → Shadow≤ R (shadowAt (κ ⊔Ctx₂ κ'))
shadowAt-⊔Ctx₂-glb {R = R} κ κ' R≤κ R≤κ' =
  pairShadowByView-glb {S = R} (ObsContext₂.S κ) (ObsContext₂.S κ') R≤κ R≤κ'

-- Context weakening is antitone on shadows:
-- stronger contexts yield finer (smaller) refinement relations.
shadowAt-antitone
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon₁ ℓORel₁ ℓOCon₂ ℓORel₂}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    {κ : ObsContext₂ C ℓOCon₁ ℓORel₁}
    {κ' : ObsContext₂ C ℓOCon₂ ℓORel₂}
  → κ ≤Ctx₂ κ'
  → Shadow≤ (shadowAt κ') (shadowAt κ)
shadowAt-antitone κ≤κ' = κ≤κ'

-- Forget observables: if `κ ≤Ctx₂ κ'` (κ weaker, κ' stronger), then
-- `thinAt κ' → thinAt κ` canonically.
forgetThin
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon₁ ℓORel₁ ℓOCon₂ ℓORel₂}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    {κ : ObsContext₂ C ℓOCon₁ ℓORel₁}
    {κ' : ObsContext₂ C ℓOCon₂ ℓORel₂}
  → κ ≤Ctx₂ κ'
  → Thin2Functor (thinAt κ') (thinAt κ)
forgetThin {C = C} {κ = κ} {κ' = κ'} κ≤κ' =
  shadowWeaken {C = C} {S = shadowAt κ'} {T = shadowAt κ}
    (shadowAt-antitone {κ = κ} {κ' = κ'} κ≤κ')
