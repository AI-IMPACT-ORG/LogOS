{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Universality.Agreement where

-- Agreement port: explicit bridge between two presented projections.
-- (Keep this as a first-class dependency, not a hidden lemma.)
-- `FidelityPort` is just the spec/obs reading of this same structure.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; _⊑_; _≈_)
open import LogOS.LT.View using (View; PullbackPreorder; _⊑[_]_; _≈[_]_)

record AgreementPort {ℓCode ℓConA ℓRelA ℓConB ℓRelB : Level}
  (X : Set ℓCode) (A : ConPreorder ℓConA ℓRelA) (B : ConPreorder ℓConB ℓRelB) :
  Set (lsuc (ℓCode ⊔ ℓConA ⊔ ℓRelA ⊔ ℓConB ⊔ ℓRelB)) where
  field
    viewA : View X A
    viewB : View X B

  infix 4 _⊑A_ _⊑B_ _≈A_ _≈B_

  _⊑A_ : X → X → Set ℓRelA
  _⊑A_ x y = x ⊑[ viewA ] y

  _⊑B_ : X → X → Set ℓRelB
  _⊑B_ x y = x ⊑[ viewB ] y

  _≈A_ : X → X → Set ℓRelA
  _≈A_ x y = x ≈[ viewA ] y

  _≈B_ : X → X → Set ℓRelB
  _≈B_ x y = x ≈[ viewB ] y

  APreorder : ConPreorder ℓCode ℓRelA
  APreorder = PullbackPreorder viewA

  BPreorder : ConPreorder ℓCode ℓRelB
  BPreorder = PullbackPreorder viewB

record AgreementContract
  {ℓCode ACon ARel BCon BRel : Level}
  {X : Set ℓCode}
  {A : ConPreorder ACon ARel}
  {B : ConPreorder BCon BRel}
  (P : AgreementPort X A B)
  : Set (lsuc (ℓCode ⊔ ACon ⊔ ARel ⊔ BCon ⊔ BRel)) where
  field
    preserve
      : ∀ {x y} → AgreementPort._⊑A_ P x y → AgreementPort._⊑B_ P x y

    reflect
      : ∀ {x y} → AgreementPort._⊑B_ P x y → AgreementPort._⊑A_ P x y

  -- Derived: mutual refinement transport follows from refinement transport.
  equivalence
    : ∀ {x y} → AgreementPort._≈A_ P x y → AgreementPort._≈B_ P x y
  equivalence (xy , yx) = (preserve xy , preserve yx)
