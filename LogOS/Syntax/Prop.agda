{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Syntax.Prop where

-- ============================================================================
-- PROPOSITIONAL CONNECTIVES
-- Logical connectives for propositional logic
-- ============================================================================
--
-- This module defines lightweight propositional connectives used throughout the
-- library for coherence and observational equality (notably `_↔_`).
--
-- The minimal truth layer continues to use Agda equality `_≡_` where appropriate;
-- `_↔_` is used to state logical equivalence without assuming function extensionality.
-- ============================================================================

-- Equality conventions (guidance)
-- - Use `_≡_` for meta-level propositional equality in Agda.
-- - Use `_↔_` for logical equivalence/coherence (pairs of functions).
-- - For decode-level equality tied to a specific kernel, prefer opening
--   `LogOS.Syntax.Eq.ForKernel K` and use `_≈K_` for decoded mutual refinement;
--   use `_≃K_` only for the strict `decode γ₁ ≡ decode γ₂` form.

open import LogOS.Prelude
open import LogOS.Prelude.Product using (_×_; Σ; _,_)

-- Logical equivalence (bi-implication)
infix 3 _↔_
record _↔_ {ℓ₁ ℓ₂ : Level} (P : Set ℓ₁) (Q : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor intro
  field
    to : P → Q
    from : Q → P

open _↔_ public

-- Standard equivalence combinators.

↔-refl : ∀ {ℓ} {P : Set ℓ} → P ↔ P
↔-refl = intro (λ x → x) (λ x → x)

↔-sym : ∀ {ℓ₁ ℓ₂} {P : Set ℓ₁} {Q : Set ℓ₂} → (P ↔ Q) → (Q ↔ P)
↔-sym pq = intro (from pq) (to pq)

↔-trans
  : ∀ {ℓ₁ ℓ₂ ℓ₃}
    {P : Set ℓ₁} {Q : Set ℓ₂} {R : Set ℓ₃}
  → (P ↔ Q) → (Q ↔ R) → (P ↔ R)
↔-trans pq qr =
  intro
    (λ p → to qr (to pq p))
    (λ r → from pq (from qr r))

-- ============================================================================
-- OBSERVATIONAL EQUALITY (generic)
-- ============================================================================

-- Observational equality induced by a satisfaction predicate.
-- This is the common pattern: two things are observationally equal iff every
-- observer (parameter `p`) cannot distinguish them. (Often called
-- “observational equivalence” in the literature.)

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

RespectsObsEqOn
  : ∀ {ℓP ℓX ℓSat}
    {P : Set ℓP} {X : Set ℓX}
  → (P → X → Set ℓSat)
  → (X → X)
  → Set (ℓP ⊔ ℓX ⊔ ℓSat)
RespectsObsEqOn Sat F = ∀ {x y} → ObsEqOn Sat x y → ObsEqOn Sat (F x) (F y)

ObsEqOn-refl
  : ∀ {ℓP ℓX ℓSat}
    {P : Set ℓP} {X : Set ℓX}
    (Sat : P → X → Set ℓSat)
    (x : X)
  → ObsEqOn Sat x x
ObsEqOn-refl Sat x _ = ↔-refl

ObsEqOn-sym
  : ∀ {ℓP ℓX ℓSat}
    {P : Set ℓP} {X : Set ℓX}
    {Sat : P → X → Set ℓSat}
    {x y : X}
  → ObsEqOn Sat x y → ObsEqOn Sat y x
ObsEqOn-sym eq p = ↔-sym (eq p)

ObsEqOn-trans
  : ∀ {ℓP ℓX ℓSat}
    {P : Set ℓP} {X : Set ℓX}
    {Sat : P → X → Set ℓSat}
    {x y z : X}
  → ObsEqOn Sat x y → ObsEqOn Sat y z → ObsEqOn Sat x z
ObsEqOn-trans xy yz p = ↔-trans (xy p) (yz p)

record ObsEqKit
  {ℓP ℓX ℓSat}
  {P : Set ℓP} {X : Set ℓX}
  (Sat : P → X → Set ℓSat)
  : Set (lsuc (ℓP ⊔ ℓX ⊔ ℓSat)) where
  field
    reflEq  : ∀ x → ObsEqOn Sat x x
    symEq   : ∀ {x y} → ObsEqOn Sat x y → ObsEqOn Sat y x
    transEq : ∀ {x y z} → ObsEqOn Sat x y → ObsEqOn Sat y z → ObsEqOn Sat x z

obsEqKit
  : ∀ {ℓP ℓX ℓSat}
    {P : Set ℓP} {X : Set ℓX}
    (Sat : P → X → Set ℓSat)
  → ObsEqKit Sat
obsEqKit Sat =
  record
    { reflEq  = ObsEqOn-refl Sat
    ; symEq   = λ {x} {y} eq → ObsEqOn-sym {Sat = Sat} eq
    ; transEq = λ {x} {y} {z} xy yz → ObsEqOn-trans {Sat = Sat} xy yz
    }

-- Conjunction (already available as _×_, but provided for logical clarity)
infixr 4 _∧_
_∧_ : ∀ {ℓ} → Set ℓ → Set ℓ → Set ℓ
P ∧ Q = P × Q

-- Disjunction (sum type)
infixr 3 _∨_
_∨_ : ∀ {ℓ} → Set ℓ → Set ℓ → Set ℓ
_∨_ {ℓ} P Q = P ⊎ Q
  where
    open import LogOS.Prelude.Sum using (_⊎_)

-- Truth (unit type): `⊤` is available via `LogOS.Prelude`.

-- Falsity (empty type)
data ⊥ {ℓ : Level} : Set ℓ where

⊥-elim : ∀ {ℓ₁ ℓ₂ : Level} {A : Set ℓ₂} → ⊥ {ℓ₁} → A
⊥-elim ()

-- Negation
infix 6 ¬_
¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬_ {ℓ} P = P → ⊥ {lzero}

-- “Existence as a witness”: a lightweight, proof-relevant inhabitance wrapper.
-- Used to name the common shape `¬ (Σ X (λ _ → ⊤))` (e.g. “no total decider”).

HasWitness : ∀ {ℓ} → Set ℓ → Set ℓ
HasWitness X = Σ X (λ _ → ⊤ {ℓ = lzero})

NoWitness : ∀ {ℓ} → Set ℓ → Set ℓ
NoWitness X = ¬ HasWitness X

-- Predicate refinement order: pointwise implication.
--
-- This is the order used when we say “largest/maximal admissible predicate” in
-- the observer/communicability developments: `P ≤Pred Q` means every witness of
-- `P a` can be transported to a witness of `Q a`.

infix 4 _≤Pred_
_≤Pred_
  : ∀ {ℓA ℓP ℓQ}
    {A : Set ℓA}
  → (A → Set ℓP)
  → (A → Set ℓQ)
  → Set (ℓA ⊔ ℓP ⊔ ℓQ)
P ≤Pred Q = ∀ a → P a → Q a

-- Decidability (constructive).
data Dec {ℓ : Level} (P : Set ℓ) : Set ℓ where
  yes : P → Dec P
  no  : (¬ P) → Dec P
