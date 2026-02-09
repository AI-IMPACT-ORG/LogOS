{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Minimal.Prequantale where

-- Minimal *prequantale* structure on a preorder (laws stated up to mutual refinement).
--
-- In standard terminology, a (unital) quantale is typically required to be a
-- *complete* join-semilattice. LogOS intentionally assumes only *finite joins*
-- (binary join + bottom) in the core, to keep models constructive and
-- prototype.
--
-- This interface is kernel-independent: it can be instantiated from
-- `QAdapter.Scale` (finite-join “budget algebra”) and also from boundary
-- preorders in concrete models.
--
-- NOTE: do not `open Prequantale` globally in large modules: many field names
-- (Con, _⊑_, _⊔_, …) are also projections and can become ambiguous under
-- `-W all -W error`. Prefer qualifying with `Prequantale.*` or opening locally.

open import LogOS.Prelude hiding (refl; trans) renaming (_⊔_ to _⊔ℓ_)
import LogOS.Prelude as Prelude

open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con
  using (ConPreorder; MonoOn; _≈CP_; ≈CP-refl; ≈CP-sym; ≈CP-trans)

record Prequantale {ℓ : Level} : Set (lsuc ℓ) where
  field
    CP : ConPreorder ℓ

  open ConPreorder CP public

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
  a ≈ b = _≈CP_ CP a b

  field
    ·-assoc    : ∀ a b c → ((a · b) · c) ≈ (a · (b · c))
    ·-idl      : ∀ a → (e · a) ≈ a
    ·-idr      : ∀ a → (a · e) ≈ a
    ·-distl-⊔  : ∀ a b c → ((a ⊔ b) · c) ≈ ((a · c) ⊔ (b · c))
    ·-distr-⊔  : ∀ a b c → (a · (b ⊔ c)) ≈ ((a · b) ⊔ (a · c))

open Prequantale public

-- --------------------------------------------------------------------------
-- Generic helpers (for working “up to ≈”)

≈-refl : ∀ {ℓ} {Q : Prequantale {ℓ}} {a : Prequantale.Con Q} → Prequantale._≈_ Q a a
≈-refl {Q = Q} {a = a} = ≈CP-refl (Prequantale.CP Q) a

≈-sym
  : ∀ {ℓ} {Q : Prequantale {ℓ}} {a b : Prequantale.Con Q}
  → Prequantale._≈_ Q a b → Prequantale._≈_ Q b a
≈-sym {Q = Q} = ≈CP-sym {CP = Prequantale.CP Q}

≈-trans
  : ∀ {ℓ} {Q : Prequantale {ℓ}} {a b c : Prequantale.Con Q}
  → Prequantale._≈_ Q a b → Prequantale._≈_ Q b c → Prequantale._≈_ Q a c
≈-trans {Q = Q} = ≈CP-trans {CP = Prequantale.CP Q}

⊔-mono
  : ∀ {ℓ} {Q : Prequantale {ℓ}} {a b c d : Prequantale.Con Q}
  → ConPreorder._⊑_ (Prequantale.CP Q) a c
  → ConPreorder._⊑_ (Prequantale.CP Q) b d
  → ConPreorder._⊑_ (Prequantale.CP Q)
      (Prequantale._⊔_ Q a b)
      (Prequantale._⊔_ Q c d)
⊔-mono {Q = Q} {a = a} {b = b} {c = c} {d = d} a≤c b≤d =
  let
    step₁ = ConPreorder.trans (Prequantale.CP Q) a≤c (Prequantale.⊔-ub₁ Q c d)
    step₂ = ConPreorder.trans (Prequantale.CP Q) b≤d (Prequantale.⊔-ub₂ Q c d)
  in Prequantale.⊔-least Q step₁ step₂

-- --------------------------------------------------------------------------
-- Adapter: any `QAdapter` induces a prequantale (in the mutual-refinement sense).

prequantaleFromQAdapter : ∀ {ℓ} → QAdapter ℓ → Prequantale {ℓ}
prequantaleFromQAdapter {ℓ} Q =
  record
    { CP = CPScale
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

    CPScale : ConPreorder ℓ
    CPScale =
      record
        { Con  = QA.Scale
        ; _⊑_  = QA._≤s_
        ; refl = QA.≤s-refl
        ; trans = QA.≤s-trans
        }

    eq→≤ : ∀ {x y : QA.Scale} → x ≡ y → QA._≤s_ x y
    eq→≤ {x = x} Prelude.refl = QA.≤s-refl {a = x}

    eq→≈ : ∀ {x y : QA.Scale} → x ≡ y → (QA._≤s_ x y × QA._≤s_ y x)
    eq→≈ eq = eq→≤ eq , eq→≤ (Prelude.sym eq)

-- --------------------------------------------------------------------------
-- Prequantale morphisms (structure-preserving maps)

record PrequantaleMor {ℓ₁ ℓ₂ : Level} (Q₁ : Prequantale {ℓ₁}) (Q₂ : Prequantale {ℓ₂})
  : Set (lsuc (ℓ₁ ⊔ℓ ℓ₂)) where
  private
    module Q1 = Prequantale Q₁
    module Q2 = Prequantale Q₂

  field
    map : Q1.Con → Q2.Con
    mono : ∀ {a b} → Q1._⊑_ a b → Q2._⊑_ (map a) (map b)
    ⊥-pres : Q2._≈_ (map Q1.⊥) Q2.⊥
    ⊔-pres : ∀ a b → Q2._≈_ (map (Q1._⊔_ a b)) (Q2._⊔_ (map a) (map b))
    e-pres : Q2._≈_ (map Q1.e) Q2.e
    ·-pres : ∀ a b → Q2._≈_ (map (Q1._·_ a b)) (Q2._·_ (map a) (map b))

open PrequantaleMor public

infix 4 _≈Mor_
_≈Mor_
  : ∀ {ℓ₁ ℓ₂ : Level} {Q₁ : Prequantale {ℓ₁}} {Q₂ : Prequantale {ℓ₂}}
  → PrequantaleMor Q₁ Q₂ → PrequantaleMor Q₁ Q₂ → Set (ℓ₁ ⊔ℓ ℓ₂)
_≈Mor_ {Q₂ = Q₂} f g =
  ∀ x → Prequantale._≈_ Q₂ (PrequantaleMor.map f x) (PrequantaleMor.map g x)
