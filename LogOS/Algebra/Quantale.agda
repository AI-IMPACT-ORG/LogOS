{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Algebra.Quantale where

-- Minimal quantale structure on a preorder (laws stated up to mutual refinement).
--
-- This sits at the “algebra” layer: it is independent of any kernel, and can be
-- instantiated from `QAdapter.Scale` (finite-join quantales) as well as from
-- boundary-constraint preorders in concrete models.
--
-- NOTE: do not `open Quantale` globally in large modules: many field names
-- (Con, _⊑_, _⊔_, …) are also projections and can become ambiguous under
-- `-W all -W error`. Prefer qualifying with `Quantale.*` or opening locally.

open import LogOS.Prelude hiding (refl; trans) renaming (_⊔_ to _⊔ℓ_)
import Agda.Builtin.Equality as Eq

open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (ConPoset; MonoOn)

record Quantale {ℓ : Level} : Set (lsuc ℓ) where
  field
    CP : ConPoset ℓ

  open ConPoset CP public

  infixl 6 _⊔_
  infixl 7 _·_

  field
    _⊔_ : Con → Con → Con
    ⊥   : Con
    ⊥-least : ∀ a → _⊑_ ⊥ a
    ⊔-ub₁  : ∀ a b → _⊑_ a (a ⊔ b)
    ⊔-ub₂  : ∀ a b → _⊑_ b (a ⊔ b)
    ⊔-least : ∀ {a b c} → _⊑_ a c → _⊑_ b c → _⊑_ (a ⊔ b) c

    _·_ : Con → Con → Con
    e   : Con

    ·-mono : ∀ {a b c d} → _⊑_ a b → _⊑_ c d → _⊑_ (a · c) (b · d)

  infix 4 _≈_
  _≈_ : Con → Con → Set ℓ
  a ≈ b = _⊑_ a b × _⊑_ b a

  field
    ·-assoc    : ∀ a b c → ((a · b) · c) ≈ (a · (b · c))
    ·-idl      : ∀ a → (e · a) ≈ a
    ·-idr      : ∀ a → (a · e) ≈ a
    ·-distl-⊔  : ∀ a b c → ((a ⊔ b) · c) ≈ ((a · c) ⊔ (b · c))
    ·-distr-⊔  : ∀ a b c → (a · (b ⊔ c)) ≈ ((a · b) ⊔ (a · c))

-- --------------------------------------------------------------------------
-- Generic helpers (for working “up to ≈”)

≈-refl : ∀ {ℓ} {Q : Quantale {ℓ}} {a : Quantale.Con Q} → Quantale._≈_ Q a a
≈-refl {Q = Q} = ConPoset.refl (Quantale.CP Q) , ConPoset.refl (Quantale.CP Q)

≈-sym
  : ∀ {ℓ} {Q : Quantale {ℓ}} {a b : Quantale.Con Q}
  → Quantale._≈_ Q a b → Quantale._≈_ Q b a
≈-sym (ab , ba) = ba , ab

≈-trans
  : ∀ {ℓ} {Q : Quantale {ℓ}} {a b c : Quantale.Con Q}
  → Quantale._≈_ Q a b → Quantale._≈_ Q b c → Quantale._≈_ Q a c
≈-trans {Q = Q} (ab , ba) (bc , cb) =
  ConPoset.trans (Quantale.CP Q) ab bc , ConPoset.trans (Quantale.CP Q) cb ba

⊔-mono
  : ∀ {ℓ} {Q : Quantale {ℓ}} {a b c d : Quantale.Con Q}
  → ConPoset._⊑_ (Quantale.CP Q) a c
  → ConPoset._⊑_ (Quantale.CP Q) b d
  → ConPoset._⊑_ (Quantale.CP Q)
      (Quantale._⊔_ Q a b)
      (Quantale._⊔_ Q c d)
⊔-mono {Q = Q} {a = a} {b = b} {c = c} {d = d} a≤c b≤d =
  let
    step₁ = ConPoset.trans (Quantale.CP Q) a≤c (Quantale.⊔-ub₁ Q c d)
    step₂ = ConPoset.trans (Quantale.CP Q) b≤d (Quantale.⊔-ub₂ Q c d)
  in Quantale.⊔-least Q step₁ step₂

-- --------------------------------------------------------------------------
-- Adapter: any `QAdapter` is a quantale (in the mutual-refinement sense).

quantaleFromQAdapter : ∀ {ℓ} → QAdapter ℓ → Quantale {ℓ}
quantaleFromQAdapter {ℓ} Q =
  record
    { CP = CP
    ; _⊔_ = QA._⊔s_
    ; ⊥   = QA.⊥s
    ; ⊥-least = QA.⊥s-least
    ; ⊔-ub₁   = QA.⊔s-ub₁
    ; ⊔-ub₂   = QA.⊔s-ub₂
    ; ⊔-least = QA.⊔s-least
    ; _·_ = QA._·_
    ; e   = QA.e
    ; ·-mono = QA.·-mono
    ; ·-assoc    = λ a b c → eq→≈ (QA.·-assoc a b c)
    ; ·-idl      = λ a → eq→≈ (QA.·-idl a)
    ; ·-idr      = λ a → eq→≈ (QA.·-idr a)
    ; ·-distl-⊔  = λ a b c → eq→≈ (QA.·-distl-⊔s a b c)
    ; ·-distr-⊔  = λ a b c → eq→≈ (QA.·-distr-⊔s a b c)
    }
  where
    module QA = QAdapter Q

    CP : ConPoset ℓ
    CP =
      record
        { Con  = QA.Scale
        ; _⊑_  = QA._≤s_
        ; refl = QA.≤s-refl
        ; trans = QA.≤s-trans
        }

    eq→≤ : ∀ {x y : QA.Scale} → x ≡ y → QA._≤s_ x y
    eq→≤ {x = x} Eq.refl = QA.≤s-refl {a = x}

    eq→≈ : ∀ {x y : QA.Scale} → x ≡ y → (QA._≤s_ x y × QA._≤s_ y x)
    eq→≈ eq = eq→≤ eq , eq→≤ (sym eq)

-- --------------------------------------------------------------------------
-- Quantale morphisms (structure-preserving maps)

record QuantaleMor {ℓ₁ ℓ₂ : Level} (Q₁ : Quantale {ℓ₁}) (Q₂ : Quantale {ℓ₂})
  : Set (lsuc (ℓ₁ ⊔ℓ ℓ₂)) where
  private
    module Q1 = Quantale Q₁
    module Q2 = Quantale Q₂

  field
    map : Q1.Con → Q2.Con
    mono : ∀ {a b} → Q1._⊑_ a b → Q2._⊑_ (map a) (map b)
    ⊥-pres : Q2._≈_ (map Q1.⊥) Q2.⊥
    ⊔-pres : ∀ a b → Q2._≈_ (map (Q1._⊔_ a b)) (Q2._⊔_ (map a) (map b))
    e-pres : Q2._≈_ (map Q1.e) Q2.e
    ·-pres : ∀ a b → Q2._≈_ (map (Q1._·_ a b)) (Q2._·_ (map a) (map b))

open QuantaleMor public

infix 4 _≈Mor_
_≈Mor_
  : ∀ {ℓ₁ ℓ₂ : Level} {Q₁ : Quantale {ℓ₁}} {Q₂ : Quantale {ℓ₂}}
  → QuantaleMor Q₁ Q₂ → QuantaleMor Q₁ Q₂ → Set (ℓ₁ ⊔ℓ ℓ₂)
_≈Mor_ {Q₂ = Q₂} f g = ∀ x → Quantale._≈_ Q₂ (QuantaleMor.map f x) (QuantaleMor.map g x)

