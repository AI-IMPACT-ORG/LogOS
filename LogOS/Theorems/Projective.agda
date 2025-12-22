{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Projective where

open import LogOS.Prelude

open import LogOS.Minimal.Con
open import LogOS.Minimal.Adjunction
open import LogOS.Minimal.Truth as Truth
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.World

-- Generic (lax) projector on a constraint poset.

-- Regularization view (module header note):
-- A Projector (nucleus) is a renormalization step on boundary truth: it is a
-- closure operator (inflationary, idempotent-lax). Its fixed points are the
-- stabilized truths. Instances arise from Flow (G-tier) and invariance
-- (H-tier), offering an operator-free fixed-point semantics complementary to
-- the HPFlow intertwining.

record Projector {ℓ : Level} (CP : ConPoset ℓ) : Set (lsuc ℓ) where
  open ConPoset CP
  field
    P        : Con → Con
    infl     : ∀ c → _⊑_ c (P c)
    idemp-lax : ∀ c → _⊑_ (P (P c)) (P c)

-- Fixed points of a projector as a poset (inherit order from CP).

record Fixed {ℓ} {CP : ConPoset ℓ} (Pr : Projector CP) : Set (lsuc ℓ) where
  infix 4 _⊑ᶠ_
  open ConPoset CP
  open Projector Pr
  field
    Conᶠ : Set ℓ
    _⊑ᶠ_ : Conᶠ → Conᶠ → Set ℓ
    reflᶠ : ∀ {x} → _⊑ᶠ_ x x
    transᶠ : ∀ {x y z} → _⊑ᶠ_ x y → _⊑ᶠ_ y z → _⊑ᶠ_ x z
    toCon : Conᶠ → Con
    fixedL : ∀ (x : Conᶠ) → _⊑_ (P (toCon x)) (toCon x)
    fixedR : ∀ (x : Conᶠ) → _⊑_ (toCon x) (P (toCon x))

-- Build the fixed-point poset by packaging both inequalities as the witness

fixedPoints
  : ∀ {ℓ} {CP : ConPoset ℓ} (Pr : Projector CP)
  → Fixed Pr
fixedPoints {CP = CP} Pr = record
  { Conᶠ  = Σ (ConPoset.Con CP)
               (λ c → ConPoset._⊑_ CP (Projector.P Pr c) c
                      × ConPoset._⊑_ CP c (Projector.P Pr c))
  ; _⊑ᶠ_   = λ x y → ConPoset._⊑_ CP (proj₁ x) (proj₁ y)
  ; reflᶠ  = ConPoset.refl CP
  ; transᶠ = ConPoset.trans CP
  ; toCon  = proj₁
  ; fixedL = λ x → fst (proj₂ x)
  ; fixedR = λ x → snd (proj₂ x)
  }

-- Instances

-- From a GuardedClosure on CP

module ForG {ℓ}
            {Sig : LogOS.Base.Signature.LogOSSignature ℓ}
            {Q   : QAdapter ℓ}
            where
  open Truth.GuardedTruth Sig Q

  fromGuarded
    : ∀ {CP : ConPoset ℓ}
      (GC : GuardedClosure CP)
    → Projector CP
  fromGuarded GC = record
    { P = GuardedClosure.Flow GC
    ; infl = GuardedClosure.infl GC
    ; idemp-lax = GuardedClosure.idemp-lax GC
    }

-- From H-tier invariance on the boundary poset

module ForH {ℓ}
             {Sig : LogOS.Base.Signature.LogOSSignature ℓ}
             {Q   : QAdapter ℓ}
             (W   : Worlds.WorldH Sig Q)
             where
  open Truth.HomotypicalTruth Sig Q W

  fromInvariance
    : (BB : BulkBoundary ℓ)
    → Invariance BB
    → Projector (BulkBoundary.bnd BB)
  fromInvariance BB Inv = record
    { P = Invariance.Inv_H Inv
    ; infl = Invariance.infl Inv
    ; idemp-lax = Invariance.idemp-lax Inv
    }
