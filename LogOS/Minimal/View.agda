{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Minimal.View where

-- View / pullback discipline for relations.
--
-- A "view" is a map from some domain `X` into a chosen semantic target preorder.
-- Domain-specific relations are introduced only as pullbacks along an explicit
-- view: `_⊑[V]_`, `_≈[V]_`, `_≃[V]_`.
--
-- This module intentionally supports both:
-- - order-theoretic targets (`ConPreorder`, where carrier and relation share a level), and
-- - observational targets induced by satisfaction (`ObsPreorder`, two-level).

open import LogOS.Prelude using (Level; _⊔_; lsuc; _≡_; sym; _,_; fst; snd)
open import LogOS.Syntax.Prop as Prop using (ObsLeOn; ObsEqOn; _↔_; intro)

open import LogOS.Minimal.Con as Con using (ConPreorder)
open import LogOS.Minimal.RelPreorder as RP using (RelPreorder; _≈RP_; ≈RP-refl; ≈RP-sym; ≈RP-trans)
open import LogOS.Minimal.RelPreorder using (≡→≈RP)

-- Embed a one-level preorder as a two-level preorder.
ConPreorder→RelPreorder : ∀ {ℓ : Level} → ConPreorder ℓ → RelPreorder ℓ ℓ
ConPreorder→RelPreorder CP =
  record
    { Con = Con.ConPreorder.Con CP
    ; _⊑_ = Con.ConPreorder._⊑_ CP
    ; refl = Con.ConPreorder.refl CP
    ; trans = Con.ConPreorder.trans CP
    }

-- A view into a semantic target preorder.
record View {ℓX ℓCon ℓRel : Level} (X : Set ℓX) (T : RelPreorder ℓCon ℓRel)
  : Set (lsuc (ℓX ⊔ ℓCon ⊔ ℓRel)) where
  field
    μ : X → RelPreorder.Con T

open View public

-- Identity view on a target preorder.
idView : ∀ {ℓCon ℓRel} (T : RelPreorder ℓCon ℓRel) → View (RelPreorder.Con T) T
idView T = record { μ = λ x → x }

-- Pullback of the target preorder along the view.
infix 4 _⊑[_]_ _≈[_]_ _≃[_]_

_⊑[_]_
  : ∀ {ℓX ℓCon ℓRel} {X : Set ℓX} {T : RelPreorder ℓCon ℓRel}
  → X → View X T → X → Set ℓRel
_⊑[_]_ {T = T} x V y = RelPreorder._⊑_ T (View.μ V x) (View.μ V y)

_≈[_]_
  : ∀ {ℓX ℓCon ℓRel} {X : Set ℓX} {T : RelPreorder ℓCon ℓRel}
  → X → View X T → X → Set ℓRel
_≈[_]_ {T = T} x V y = _≈RP_ T (View.μ V x) (View.μ V y)

-- Pullback of strict Agda equality along the view ("strict meaning equality").
_≃[_]_
  : ∀ {ℓX ℓCon ℓRel} {X : Set ℓX} {T : RelPreorder ℓCon ℓRel}
  → X → View X T → X → Set ℓCon
x ≃[ V ] y = View.μ V x ≡ View.μ V y

-- ============================================================================
-- Extensionality kits (view-based)
-- ============================================================================

Extensional≃
  : ∀ {ℓX ℓCon ℓRel ℓP}
    {X : Set ℓX} {T : RelPreorder ℓCon ℓRel}
  → View X T
  → (X → Set ℓP)
  → Set (ℓX ⊔ ℓCon ⊔ ℓP)
Extensional≃ V P = ∀ x y → x ≃[ V ] y → P x → P y

Extensional≃-cong
  : ∀ {ℓX ℓCon ℓRel ℓP}
    {X : Set ℓX} {T : RelPreorder ℓCon ℓRel}
    {V : View X T} {P : X → Set ℓP}
  → Extensional≃ V P
  → ∀ {x y} → x ≃[ V ] y → P x ↔ P y
Extensional≃-cong ext eq =
  intro
    (λ p → ext _ _ eq p)
    (λ p → ext _ _ (sym eq) p)

Extensional≈
  : ∀ {ℓX ℓCon ℓRel ℓP}
    {X : Set ℓX} {T : RelPreorder ℓCon ℓRel}
  → View X T
  → (X → Set ℓP)
  → Set (ℓX ⊔ ℓRel ⊔ ℓP)
Extensional≈ V P = ∀ x y → x ≈[ V ] y → P x → P y

Extensional≈-cong
  : ∀ {ℓX ℓCon ℓRel ℓP}
    {X : Set ℓX} {T : RelPreorder ℓCon ℓRel}
    {V : View X T} {P : X → Set ℓP}
  → Extensional≈ V P
  → ∀ {x y} → x ≈[ V ] y → P x ↔ P y
Extensional≈-cong {T = T} ext eq =
  intro
    (λ p → ext _ _ eq p)
    (λ p → ext _ _ (≈RP-sym {RP = T} eq) p)

-- View composition: views compose by function composition on `μ`.
infixr 40 _∘View_
_∘View_
  : ∀ {ℓX ℓY ℓZ ℓRelY ℓRelZ}
    {X : Set ℓX}
    {TY : RelPreorder ℓY ℓRelY}
    {TZ : RelPreorder ℓZ ℓRelZ}
  → View (RelPreorder.Con TY) TZ
  → View X TY
  → View X TZ
_∘View_ V₂ V₁ = record { μ = λ x → View.μ V₂ (View.μ V₁ x) }

-- The preorder on the domain induced by a view (pullback preorder).
PullbackPreorder
  : ∀ {ℓX ℓCon ℓRel} {X : Set ℓX} {T : RelPreorder ℓCon ℓRel}
  → View X T
  → RelPreorder ℓX ℓRel
PullbackPreorder {X = X} {T = T} V =
  record
    { Con = X
    ; _⊑_ = λ x y → x ⊑[ V ] y
    ; refl = RelPreorder.refl T
    ; trans = RelPreorder.trans T
    }

-- `≈[V]` is definitionally the mutual refinement in the pullback preorder.
≈[V]↔Pullback≈
  : ∀ {ℓX ℓCon ℓRel} {X : Set ℓX} {T : RelPreorder ℓCon ℓRel}
    {V : View X T} {x y : X}
  → x ≈[ V ] y ↔ _≈RP_ (PullbackPreorder V) x y
≈[V]↔Pullback≈ = intro (λ p → p) (λ p → p)

-- Directional projections (canonical names).
≈[V]⇒
  : ∀ {ℓX ℓCon ℓRel} {X : Set ℓX} {T : RelPreorder ℓCon ℓRel}
    {V : View X T} {x y : X}
  → x ≈[ V ] y
  → x ⊑[ V ] y
≈[V]⇒ (xy , _) = xy

≈[V]⇐
  : ∀ {ℓX ℓCon ℓRel} {X : Set ℓX} {T : RelPreorder ℓCon ℓRel}
    {V : View X T} {x y : X}
  → x ≈[ V ] y
  → y ⊑[ V ] x
≈[V]⇐ (_ , yx) = yx

-- Basic equivalence kit for `≈[V]` (inherits from the target preorder).
≈[V]-refl
  : ∀ {ℓX ℓCon ℓRel} {X : Set ℓX} {T : RelPreorder ℓCon ℓRel}
    (V : View X T) (x : X)
  → x ≈[ V ] x
≈[V]-refl {T = T} V x = ≈RP-refl T (View.μ V x)

-- Strict pullback equality implies mutual refinement in the target preorder.
≃→≈[V]
  : ∀ {ℓX ℓCon ℓRel} {X : Set ℓX} {T : RelPreorder ℓCon ℓRel}
    {V : View X T} {x y : X}
  → x ≃[ V ] y
  → x ≈[ V ] y
≃→≈[V] {T = T} eq = ≡→≈RP {RP = T} eq

≈[V]-sym
  : ∀ {ℓX ℓCon ℓRel} {X : Set ℓX} {T : RelPreorder ℓCon ℓRel}
    {V : View X T} {x y : X}
  → x ≈[ V ] y → y ≈[ V ] x
≈[V]-sym {T = T} = ≈RP-sym {RP = T}

≈[V]-trans
  : ∀ {ℓX ℓCon ℓRel} {X : Set ℓX} {T : RelPreorder ℓCon ℓRel}
    {V : View X T} {x y z : X}
  → x ≈[ V ] y → y ≈[ V ] z → x ≈[ V ] z
≈[V]-trans {T = T} = ≈RP-trans {RP = T}

-- ============================================================================
-- Observational targets as first-class view targets
-- ============================================================================

ObsPreorder
  : ∀ {ℓP ℓX ℓSat}
    {P : Set ℓP} {X : Set ℓX}
  → (Sat : P → X → Set ℓSat)
  → RelPreorder ℓX (ℓP ⊔ ℓSat)
ObsPreorder {P = P} {X = X} Sat =
  record
    { Con = X
    ; _⊑_ = ObsLeOn Sat
    ; refl = λ {x} p sat → sat
    ; trans = λ {a} {b} {c} ab bc p sat → bc p (ab p sat)
    }

-- Observational mutual refinement is definitionally `≈` in `ObsPreorder`.
Obs≈
  : ∀ {ℓP ℓX ℓSat}
    {P : Set ℓP} {X : Set ℓX}
    (Sat : P → X → Set ℓSat)
  → X → X → Set (ℓP ⊔ ℓSat)
Obs≈ Sat = _≈RP_ (ObsPreorder Sat)

Obs≈⇒
  : ∀ {ℓP ℓX ℓSat}
    {P : Set ℓP} {X : Set ℓX}
    {Sat : P → X → Set ℓSat}
    {x y : X}
  → Obs≈ Sat x y
  → ObsLeOn Sat x y
Obs≈⇒ (xy , _) = xy

Obs≈⇐
  : ∀ {ℓP ℓX ℓSat}
    {P : Set ℓP} {X : Set ℓX}
    {Sat : P → X → Set ℓSat}
    {x y : X}
  → Obs≈ Sat x y
  → ObsLeOn Sat y x
Obs≈⇐ (_ , yx) = yx

-- Bridge: the usual `ObsEqOn` is logically equivalent to `Obs≈` (two-way ObsLe).
ObsEqOn↔Obs≈
  : ∀ {ℓP ℓX ℓSat}
    {P : Set ℓP} {X : Set ℓX}
    (Sat : P → X → Set ℓSat)
    {x y : X}
  → ObsEqOn Sat x y ↔ Obs≈ Sat x y
ObsEqOn↔Obs≈ Sat {x} {y} =
  Prop.ObsEqOn↔ObsLeOn {Sat = Sat} {x = x} {y = y}
