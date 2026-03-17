{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Syntax.Prop where

-- Minimal propositional connectives (stdlib-independent).

open import LogOS.Prelude
infixr 4 _∧_
_∧_ : ∀ {ℓ} → Set ℓ → Set ℓ → Set ℓ
P ∧ Q = P × Q

infix 3 _↔_
record _↔_ {ℓ₁ ℓ₂ : Level} (P : Set ℓ₁) (Q : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor intro
  field
    to   : P → Q
    from : Q → P

open _↔_ public
↔-refl : ∀ {ℓ} {P : Set ℓ} → P ↔ P
↔-refl = intro (λ x → x) (λ x → x)

↔-sym : ∀ {ℓ₁ ℓ₂} {P : Set ℓ₁} {Q : Set ℓ₂} → P ↔ Q → Q ↔ P
↔-sym pq = intro (from pq) (to pq)

↔-trans
  : ∀ {ℓ₁ ℓ₂ ℓ₃}
    {P : Set ℓ₁} {Q : Set ℓ₂} {R : Set ℓ₃}
  → P ↔ Q
  → Q ↔ R
  → P ↔ R
↔-trans pq qr =
  intro
    (λ p → to qr (to pq p))
    (λ r → from pq (from qr r))

-- ============================================================================
-- Observational relations (generic)
-- ============================================================================

-- Observational equality induced by a satisfaction predicate:
-- two things are observationally equal iff every observer cannot distinguish them.

ObsEqOn
  : ∀ {ℓP ℓX ℓSat}
    {P : Set ℓP} {X : Set ℓX}
  → (P → X → Set ℓSat)
  → X → X → Set (ℓP ⊔ ℓSat)
ObsEqOn Sat x y = ∀ p → Sat p x ↔ Sat p y

-- Observational preorder induced by a satisfaction predicate.

ObsLeOn
  : ∀ {ℓP ℓX ℓSat}
    {P : Set ℓP} {X : Set ℓX}
  → (P → X → Set ℓSat)
  → X → X → Set (ℓP ⊔ ℓSat)
ObsLeOn Sat x y = ∀ p → Sat p x → Sat p y

ObsEqOn↔ObsLeOn
  : ∀ {ℓP ℓX ℓSat}
    {P : Set ℓP} {X : Set ℓX}
    {Sat : P → X → Set ℓSat}
    {x y : X}
  → ObsEqOn Sat x y ↔ (ObsLeOn Sat x y × ObsLeOn Sat y x)
ObsEqOn↔ObsLeOn {Sat = Sat} {x} {y} =
  intro
    (λ eq →
      ( (λ p sat → to (eq p) sat)
      , (λ p sat → from (eq p) sat)
      ))
    (λ (xy , yx) p → intro (xy p) (yx p))
