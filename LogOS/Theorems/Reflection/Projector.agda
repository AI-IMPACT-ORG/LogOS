{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Reflection.Projector where

-- Shared “closure / projector / nucleus” shape.
--
-- The LogOS library uses several endomaps that behave like stabilisation steps:
-- - Guarded closure (G-tier): `Flow`
-- - Invariance (H-tier): `Inv_H`
-- - Bulk↔boundary adjunction: `T = bnd ∘ ext` (boundary closure)
--
-- This module isolates the common record shape so downstream theorems can talk
-- about “a projector on a preorder” without tying themselves to any specific tier.

open import LogOS.Prelude

open import LogOS.Minimal.Con using (ConPreorder; PartialOrder; MonoOn; _≈CP_)
open import LogOS.Minimal.Closure using (ClosureOp)

-- A (lax) projector on a constraint preorder: inflationary and idempotent-lax.
-- Monotonicity is intentionally not required: some reflection steps are only
-- assumed to satisfy the stabilisation laws.

record Projector {ℓ : Level} (CP : ConPreorder ℓ) : Set (lsuc ℓ) where
  open ConPreorder CP
  field
    P         : Con → Con
    infl      : ∀ c → _⊑_ c (P c)
    idemp-lax : ∀ c → _⊑_ (P (P c)) (P c)

open Projector public

-- Dual shape: a (lax) coreflector / interior operator.
--
-- The direction of “deflation” is reversed: I c ⊑ c. As with `Projector`,
-- we do not require monotonicity here; only the stabilisation laws.

record Coreflector {ℓ : Level} (CP : ConPreorder ℓ) : Set (lsuc ℓ) where
  open ConPreorder CP
  field
    I         : Con → Con
    defl      : ∀ c → _⊑_ (I c) c
    idemp-lax : ∀ c → _⊑_ (I (I c)) (I c)

open Coreflector public

-- Fixed points of a coreflector (stable interiors), again packaged via both
-- inequalities to avoid antisymmetry requirements.

record FixedI {ℓ} {CP : ConPreorder ℓ} (Co : Coreflector CP) : Set (lsuc ℓ) where
  infix 4 _⊑ᶠᶦ_
  open ConPreorder CP
  field
    Conᶠᶦ   : Set ℓ
    _⊑ᶠᶦ_   : Conᶠᶦ → Conᶠᶦ → Set ℓ
    reflᶠᶦ  : ∀ {x} → _⊑ᶠᶦ_ x x
    transᶠᶦ : ∀ {x y z} → _⊑ᶠᶦ_ x y → _⊑ᶠᶦ_ y z → _⊑ᶠᶦ_ x z
    toConᶦ  : Conᶠᶦ → Con
    fixedLᶦ : ∀ (x : Conᶠᶦ) → _⊑_ (Coreflector.I Co (toConᶦ x)) (toConᶦ x)
    fixedRᶦ : ∀ (x : Conᶠᶦ) → _⊑_ (toConᶦ x) (Coreflector.I Co (toConᶦ x))

open FixedI public

fixedPointsI
  : ∀ {ℓ} {CP : ConPreorder ℓ} (Co : Coreflector CP)
  → FixedI Co
fixedPointsI {CP = CP} Co = record
  { Conᶠᶦ  = Σ (ConPreorder.Con CP)
               (λ c → ConPreorder._⊑_ CP (Coreflector.I Co c) c
                      × ConPreorder._⊑_ CP c (Coreflector.I Co c))
  ; _⊑ᶠᶦ_   = λ x y → ConPreorder._⊑_ CP (proj₁ x) (proj₁ y)
  ; reflᶠᶦ  = ConPreorder.refl CP
  ; transᶠᶦ = ConPreorder.trans CP
  ; toConᶦ  = proj₁
  ; fixedLᶦ = λ x → fst (proj₂ x)
  ; fixedRᶦ = λ x → snd (proj₂ x)
  }

-- Fixed points of a projector as a preorder (inherit order from CP).
--
-- We package both inequalities to avoid needing antisymmetry.

record Fixed {ℓ} {CP : ConPreorder ℓ} (Pr : Projector CP) : Set (lsuc ℓ) where
  infix 4 _⊑ᶠ_
  open ConPreorder CP
  field
    Conᶠ   : Set ℓ
    _⊑ᶠ_   : Conᶠ → Conᶠ → Set ℓ
    reflᶠ  : ∀ {x} → _⊑ᶠ_ x x
    transᶠ : ∀ {x y z} → _⊑ᶠ_ x y → _⊑ᶠ_ y z → _⊑ᶠ_ x z
    toCon  : Conᶠ → Con
    fixedL : ∀ (x : Conᶠ) → _⊑_ (Projector.P Pr (toCon x)) (toCon x)
    fixedR : ∀ (x : Conᶠ) → _⊑_ (toCon x) (Projector.P Pr (toCon x))

open Fixed public

-- Build the fixed-point preorder by packaging both inequalities as the witness.

fixedPoints
  : ∀ {ℓ} {CP : ConPreorder ℓ} (Pr : Projector CP)
  → Fixed Pr
fixedPoints {CP = CP} Pr = record
  { Conᶠ  = Σ (ConPreorder.Con CP)
               (λ c → ConPreorder._⊑_ CP (Projector.P Pr c) c
                      × ConPreorder._⊑_ CP c (Projector.P Pr c))
  ; _⊑ᶠ_   = λ x y → ConPreorder._⊑_ CP (proj₁ x) (proj₁ y)
  ; reflᶠ  = ConPreorder.refl CP
  ; transᶠ = ConPreorder.trans CP
  ; toCon  = proj₁
  ; fixedL = λ x → fst (proj₂ x)
  ; fixedR = λ x → snd (proj₂ x)
  }

-- --------------------------------------------------------------------------
-- Conversions: ClosureOp ↔ Projector
--
-- `ClosureOp` is the monotone “nucleus/closure” interface used by modality/μ
-- tooling, while `Projector` is the lighter “inflationary + idempotent‑lax”
-- shape used to talk about fixed points without assuming monotonicity.
-- --------------------------------------------------------------------------

projectorOfClosureOp
  : ∀ {ℓ} {CP : ConPreorder ℓ}
  → ClosureOp CP → Projector CP
projectorOfClosureOp C =
  record
    { P         = ClosureOp.cl C
    ; infl      = ClosureOp.infl C
    ; idemp-lax = ClosureOp.idemp-lax C
    }

closureOpOfProjector
  : ∀ {ℓ} {CP : ConPreorder ℓ}
  → (Pr : Projector CP)
  → MonoOn CP (Projector.P Pr)
  → ClosureOp CP
closureOpOfProjector Pr monoP =
  record
    { cl        = Projector.P Pr
    ; mono      = monoP
    ; infl      = Projector.infl Pr
    ; idemp-lax = Projector.idemp-lax Pr
    }

-- Convenience bundles --------------------------------------------------------

-- A projector together with monotonicity. This is enough to view it as a
-- `ClosureOp` (nucleus) without threading a separate `MonoOn` argument.

record ProjectorMono {ℓ : Level} (CP : ConPreorder ℓ) : Set (lsuc ℓ) where
  field
    core   : Projector CP
    mono-P : MonoOn CP (Projector.P core)

  open Projector core public

  asClosureOp : ClosureOp CP
  asClosureOp = closureOpOfProjector core mono-P

  -- Derived idempotence as mutual refinement (no antisymmetry needed).

  idemp≈
    : ∀ c → _≈CP_ CP (Projector.P core c) (Projector.P core (Projector.P core c))
  idemp≈ c =
    ( mono-P (Projector.infl core c)
    , Projector.idemp-lax core c
    )

-- A coreflector together with monotonicity (the “interior” analogue).

record CoreflectorMono {ℓ : Level} (CP : ConPreorder ℓ) : Set (lsuc ℓ) where
  field
    core    : Coreflector CP
    mono-I  : MonoOn CP (Coreflector.I core)

  open Coreflector core public

-- Any `ClosureOp` yields a monotone projector immediately.

projectorMonoOfClosureOp
  : ∀ {ℓ} {CP : ConPreorder ℓ}
  → ClosureOp CP
  → ProjectorMono CP
projectorMonoOfClosureOp C =
  record
    { core = projectorOfClosureOp C
    ; mono-P = ClosureOp.mono C
    }

-- Antisymmetry upgrades mutual refinement on `ProjectorMono` to equality.

idemp≡
  : ∀ {ℓ} {CP : ConPreorder ℓ}
  → PartialOrder CP
  → (PM : ProjectorMono CP)
  → ∀ c → Projector.P (ProjectorMono.core PM) (Projector.P (ProjectorMono.core PM) c)
        ≡ Projector.P (ProjectorMono.core PM) c
idemp≡ {CP = CP} po PM c =
  let
    open ConPreorder CP
    open Projector (ProjectorMono.core PM)
  in
  PartialOrder.antisym po
    (Projector.idemp-lax (ProjectorMono.core PM) c)
    (ProjectorMono.mono-P PM (Projector.infl (ProjectorMono.core PM) c))
