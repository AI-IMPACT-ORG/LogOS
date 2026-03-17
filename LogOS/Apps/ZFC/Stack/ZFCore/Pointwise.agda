{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.ZFCore.Pointwise where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)
open import LogOS.LT.View using (μ)

open import LogOS.Apps.ZFC.Stack.ZFCore.Context using (SetContext)
import LogOS.Apps.ZFC.Stack.ZFCore.Signature as Signature
open Signature using (ZFSignature)
open import LogOS.Apps.ZFC.Stack.ZFCore.Laws using (ZFLaws)

-- “Pointwise first” packaging of the ZF constructor laws.
--
-- Motivation:
-- the ZF constructor laws are naturally stated per membership probe `z`.
-- This record makes the per-probe obligation layer explicit, so downstream
-- constructions can:
-- - consume laws pointwise (common in locality-style arguments), and
-- - optionally repackage them into bundled/global statements.

record ZFMembershipLawsAt
  {ℓ : Level}
  (C : SetContext {ℓ})
  (Sig : ZFSignature C)
  (z : SetContext.SetU C)
  : Set (lsuc ℓ) where
  open SetContext C
  open ZFSignature Sig
  module D = Signature.Derived Sig

  field
    emptyAt
      : ¬ (z ∈ μ EmptyV tt)

    pairingAt
      : ∀ x y
      → (z ∈ μ PairV (x , y)) ↔ ((z ≈ x) ⊎ (z ≈ y))

    unionAt
      : ∀ x
      → (z ∈ μ UnionV x) ↔ (Σ SetU (λ y → (y ∈ x) × (z ∈ y)))

    powersetAt
      : ∀ x
      → (z ∈ μ PowersetV x) ↔ (∀ w → w ∈ z → w ∈ x)

    infinityAt
      : (z ∈ μ OmegaV tt)
          ↔ ((z ≈ μ D.ZeroV tt)
            ⊎ (Σ SetU (λ y → y ∈ μ OmegaV tt × (z ≈ μ D.SuccV y))))

    separationAt
      : ∀ (P : SetU → Set ℓ) x
      → (z ∈ μ (SeparationV P) x) ↔ ((z ∈ x) × (P z))

    replacementAt
      : ∀ (R : SetU → SetU → Set ℓ) x
      → (z ∈ μ (ReplacementV R) x) ↔ (Σ SetU (λ u → u ∈ x × R u z))

record ZFLawsPointwise {ℓ : Level} (C : SetContext {ℓ}) (Sig : ZFSignature C)
  : Set (lsuc ℓ) where
  open SetContext C
  open ZFSignature Sig

  field
    membershipLawsAt : (z : SetU) → ZFMembershipLawsAt C Sig z

    foundation
      : ∀ x
      → (Σ SetU (λ y → y ∈ x))
      → (Σ SetU (λ y → y ∈ x × (∀ z → z ∈ x → ¬ (z ∈ y))))

-- Conversions between the original “bundled” law record and the pointwise view.

toPointwiseLaws
  : ∀ {ℓ : Level} {C : SetContext {ℓ}} {Sig : ZFSignature C}
  → ZFLaws C Sig
  → ZFLawsPointwise C Sig
toPointwiseLaws laws =
  record
    { membershipLawsAt =
        λ z →
          record
            { emptyAt = empty-spec z
            ; pairingAt = λ x y → pairing-spec x y z
            ; unionAt = λ x → union-spec x z
            ; powersetAt = λ x → powerset-spec x z
            ; infinityAt = infinity-spec z
            ; separationAt = λ P x → separation-spec P x z
            ; replacementAt = λ R x → replacement-spec R x z
            }
    ; foundation = foundation
    }
  where
    open ZFLaws laws

fromPointwiseLaws
  : ∀ {ℓ : Level} {C : SetContext {ℓ}} {Sig : ZFSignature C}
  → ZFLawsPointwise C Sig
  → ZFLaws C Sig
fromPointwiseLaws pw =
  record
    { coreLaws =
        record
          { empty-spec = λ z → ZFMembershipLawsAt.emptyAt (membershipLawsAt z)
          ; pairing-spec = λ x y z → ZFMembershipLawsAt.pairingAt (membershipLawsAt z) x y
          ; union-spec = λ x z → ZFMembershipLawsAt.unionAt (membershipLawsAt z) x
          }
    ; powersetLaws =
        record
          { powerset-spec = λ x z → ZFMembershipLawsAt.powersetAt (membershipLawsAt z) x }
    ; infinityLaws =
        record
          { infinity-spec = λ z → ZFMembershipLawsAt.infinityAt (membershipLawsAt z) }
    ; separationLaws =
        record
          { separation-spec = λ P x z → ZFMembershipLawsAt.separationAt (membershipLawsAt z) P x }
    ; replacementLaws =
        record
          { replacement-spec = λ R x z → ZFMembershipLawsAt.replacementAt (membershipLawsAt z) R x }
    ; foundationLaws =
        record
          { foundation = foundation }
    }
  where
    open ZFLawsPointwise pw
