{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.View where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- View / pullback discipline (minimal, ConPreorder-only).
--
-- A "view" is a map into a chosen semantic target preorder.
-- Domain-specific relations should be introduced as pullbacks along explicit
-- views: `_⊑[ V ]_`, `_≈[ V ]_`.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder as Con using (ConPreorder; Con; _⊑_; _≈_; _×CP_)
open import LogOS.Syntax.Prop using (_↔_; intro)

record View {ℓX ℓCon ℓRel : Level} (X : Set ℓX) (T : ConPreorder ℓCon ℓRel)
  : Set (lsuc (ℓX ⊔ ℓCon ⊔ ℓRel)) where
  field
    μ : X → Con T

open View public

-- Role-tagged wrappers around `View`.
--
-- Public interfaces often reuse the same underlying `View` encoding for
-- semantically distinct purposes. These wrappers preserve the encoding but keep
-- the intended role visible in types.

data ViewRole : Set where
  decodeR probeR transportR obsR programR presentationR : ViewRole

record RoleView
  (r : ViewRole)
  {ℓX ℓCon ℓRel : Level}
  (X : Set ℓX)
  (T : ConPreorder ℓCon ℓRel)
  : Set (lsuc (ℓX ⊔ ℓCon ⊔ ℓRel)) where
  constructor mkRoleView
  field
    V : View X T

open RoleView public

forget
  : ∀ {r ℓX ℓCon ℓRel}
    {X : Set ℓX}
    {T : ConPreorder ℓCon ℓRel}
  → RoleView r X T
  → View X T
forget rv = V rv

μᵣ
  : ∀ {r ℓX ℓCon ℓRel}
    {X : Set ℓX}
    {T : ConPreorder ℓCon ℓRel}
  → RoleView r X T
  → X
  → Con T
μᵣ rv x = μ (forget rv) x

DecodeView = RoleView decodeR
ProbeView = RoleView probeR
TransportView = RoleView transportR
ObsView = RoleView obsR
ProgramView = RoleView programR
PresentationView = RoleView presentationR

idView : ∀ {ℓCon ℓRel} (T : ConPreorder ℓCon ℓRel) → View (Con T) T
idView T = record { μ = λ x → x }

-- Reindex/pull back a view along a map.
pullbackView
  : ∀ {ℓX ℓY ℓCon ℓRel}
    {X : Set ℓX} {Y : Set ℓY} {T : ConPreorder ℓCon ℓRel}
  → (f : Y → X)
  → View X T
  → View Y T
pullbackView f V = record { μ = λ y → μ V (f y) }

infix 4 _⊑[_]_ _≈[_]_

_⊑[_]_
  : ∀ {ℓX ℓCon ℓRel} {X : Set ℓX} {T : ConPreorder ℓCon ℓRel}
  → X → View X T → X → Set ℓRel
_⊑[_]_ {T = T} x V y = _⊑_ T (μ V x) (μ V y)

_≈[_]_
  : ∀ {ℓX ℓCon ℓRel} {X : Set ℓX} {T : ConPreorder ℓCon ℓRel}
  → X → View X T → X → Set ℓRel
_≈[_]_ {T = T} x V y = _≈_ T (μ V x) (μ V y)

infixr 40 _∘View_
_∘View_
  : ∀ {ℓX ℓYCon ℓYRel ℓZCon ℓZRel}
    {X : Set ℓX}
    {TY : ConPreorder ℓYCon ℓYRel}
    {TZ : ConPreorder ℓZCon ℓZRel}
  → View (Con TY) TZ
  → View X TY
  → View X TZ
_∘View_ V₂ V₁ = record { μ = λ x → μ V₂ (μ V₁ x) }

-- Product/distributed observation: pair two independent views.
--
-- Reading: extend observation by adding an extra probe suite/channel.
-- This makes “meaning injection” explicit: the induced pullback refinement
-- requires refinement in *both* observed components.
pairView
  : ∀ {ℓX ℓCon₁ ℓRel₁ ℓCon₂ ℓRel₂}
    {X : Set ℓX}
    {O₁ : ConPreorder ℓCon₁ ℓRel₁}
    {O₂ : ConPreorder ℓCon₂ ℓRel₂}
  → View X O₁
  → View X O₂
  → View X (O₁ ×CP O₂)
pairView V₁ V₂ = record { μ = λ x → (μ V₁ x , μ V₂ x) }

pairView-fst
  : ∀ {ℓX ℓCon₁ ℓRel₁ ℓCon₂ ℓRel₂}
    {X : Set ℓX}
    {O₁ : ConPreorder ℓCon₁ ℓRel₁}
    {O₂ : ConPreorder ℓCon₂ ℓRel₂}
    {V₁ : View X O₁} {V₂ : View X O₂}
    {x y : X}
  → x ⊑[ pairView V₁ V₂ ] y
  → x ⊑[ V₁ ] y
pairView-fst le = fst le

pairView-snd
  : ∀ {ℓX ℓCon₁ ℓRel₁ ℓCon₂ ℓRel₂}
    {X : Set ℓX}
    {O₁ : ConPreorder ℓCon₁ ℓRel₁}
    {O₂ : ConPreorder ℓCon₂ ℓRel₂}
    {V₁ : View X O₁} {V₂ : View X O₂}
    {x y : X}
  → x ⊑[ pairView V₁ V₂ ] y
  → x ⊑[ V₂ ] y
pairView-snd le = snd le

pairView-intro
  : ∀ {ℓX ℓCon₁ ℓRel₁ ℓCon₂ ℓRel₂}
    {X : Set ℓX}
    {O₁ : ConPreorder ℓCon₁ ℓRel₁}
    {O₂ : ConPreorder ℓCon₂ ℓRel₂}
    {V₁ : View X O₁} {V₂ : View X O₂}
    {x y : X}
  → x ⊑[ V₁ ] y
  → x ⊑[ V₂ ] y
  → x ⊑[ pairView V₁ V₂ ] y
pairView-intro le₁ le₂ = (le₁ , le₂)

-- ============================================================================
-- View extensionality kits
-- ============================================================================

-- The induced preorder on the domain (pull back refinement along `μ`).
PullbackPreorder
  : ∀ {ℓX ℓCon ℓRel} {X : Set ℓX} {T : ConPreorder ℓCon ℓRel}
  → View X T
  → ConPreorder ℓX ℓRel
PullbackPreorder {X = X} {T = T} V =
  record
    { Con   = X
    ; _⊑_   = λ x y → x ⊑[ V ] y
    ; refl  = λ {x} → ConPreorder.refl T {c = μ V x}
    ; trans =
        λ {x} {y} {z} xy yz →
          let
            module R = LogOS.Prelude.RefinementKit.Reasoning T
          in
          R._⊑⟨_⟩_ (μ V x) xy yz
    }

-- Extensionality for predicates w.r.t. mutual refinement of observed meaning.
Extensional≈
  : ∀ {ℓX ℓCon ℓRel ℓP}
    {X : Set ℓX} {T : ConPreorder ℓCon ℓRel}
  → View X T
  → (X → Set ℓP)
  → Set (ℓX ⊔ ℓRel ⊔ ℓP)
Extensional≈ V P = ∀ x y → x ≈[ V ] y → P x → P y

Extensional≈-cong
  : ∀ {ℓX ℓCon ℓRel ℓP}
    {X : Set ℓX} {T : ConPreorder ℓCon ℓRel}
    {V : View X T} {P : X → Set ℓP}
  → Extensional≈ V P
  → ∀ {x y} → x ≈[ V ] y → P x ↔ P y
Extensional≈-cong ext (xy , yx) =
  intro
    (λ p → ext _ _ (xy , yx) p)
    (λ p → ext _ _ (yx , xy) p)

-- Extensionality for binary relations w.r.t. mutual refinement of observed
-- meaning in each argument.
ExtensionalRel≈
  : ∀ {ℓX ℓCon ℓRel ℓR}
    {X : Set ℓX} {T : ConPreorder ℓCon ℓRel}
  → View X T
  → (X → X → Set ℓR)
  → Set (ℓX ⊔ ℓRel ⊔ ℓR)
ExtensionalRel≈ V R =
  ∀ x x' y y'
  → x ≈[ V ] x'
  → y ≈[ V ] y'
  → R x y
  → R x' y'

ExtensionalRel≈-cong
  : ∀ {ℓX ℓCon ℓRel ℓR}
    {X : Set ℓX} {T : ConPreorder ℓCon ℓRel}
    {V : View X T} {R : X → X → Set ℓR}
  → ExtensionalRel≈ V R
  → ∀ {x x' y y'}
  → x ≈[ V ] x'
  → y ≈[ V ] y'
  → R x y ↔ R x' y'
ExtensionalRel≈-cong ext xx' yy' =
  intro
    (λ rxy → ext _ _ _ _ xx' yy' rxy)
    (λ rx'y' → ext _ _ _ _ (snd xx' , fst xx') (snd yy' , fst yy') rx'y')
