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

open import LogOS.Minimal.Adapter using (QAdapter; QAdapterCore; QAdapterEqLaws; qAdapterCore; qAdapterEqLaws)
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

record ScaleLaxLaws {ℓ : Level} (C : QAdapterCore ℓ) : Set (lsuc ℓ) where
  module QC = QAdapterCore C

  infix 4 _≈s_
  _≈s_ : QC.Scale → QC.Scale → Set ℓ
  x ≈s y = QC._≤s_ x y × QC._≤s_ y x

  field
    ·-assoc    : ∀ a b c → QC._·_ (QC._·_ a b) c ≈s QC._·_ a (QC._·_ b c)
    ·-idl      : ∀ a → QC._·_ QC.e a ≈s a
    ·-idr      : ∀ a → QC._·_ a QC.e ≈s a
    ·-distl-⊔  : ∀ a b c → QC._·_ (QC._⊔s_ a b) c ≈s QC._⊔s_ (QC._·_ a c) (QC._·_ b c)
    ·-distr-⊔  : ∀ a b c → QC._·_ a (QC._⊔s_ b c) ≈s QC._⊔s_ (QC._·_ a b) (QC._·_ a c)

scaleLaxLawsFromEq
  : ∀ {ℓ} {C : QAdapterCore ℓ}
  → QAdapterEqLaws C
  → ScaleLaxLaws C
scaleLaxLawsFromEq {C = C} E =
  record
    { ·-assoc    = λ a b c → eq→≈ (QAdapterEqLaws.·-assoc E a b c)
    ; ·-idl      = λ a → eq→≈ (QAdapterEqLaws.·-idl E a)
    ; ·-idr      = λ a → eq→≈ (QAdapterEqLaws.·-idr E a)
    ; ·-distl-⊔  = λ a b c → eq→≈ (QAdapterEqLaws.·-distl-⊔s E a b c)
    ; ·-distr-⊔  = λ a b c → eq→≈ (QAdapterEqLaws.·-distr-⊔s E a b c)
    }
  where
    module QC = QAdapterCore C

    eq→≤ : ∀ {x y : QC.Scale} → x ≡ y → QC._≤s_ x y
    eq→≤ {x = x} Prelude.refl = QC.≤s-refl {a = x}

    eq→≈ : ∀ {x y : QC.Scale} → x ≡ y → (QC._≤s_ x y × QC._≤s_ y x)
    eq→≈ eq = eq→≤ eq , eq→≤ (Prelude.sym eq)

prequantaleFromCoreLax : ∀ {ℓ} → (C : QAdapterCore ℓ) → ScaleLaxLaws C → Prequantale {ℓ}
prequantaleFromCoreLax {ℓ} C L =
  record
    { CP = CPScale
    ; _⊔_ = QC._⊔s_
    ; ⊥   = QC.⊥s
    ; ⊥-least = QC.⊥s-least
    ; ⊔-ub₁   = QC.⊔s-ub₁
    ; ⊔-ub₂   = QC.⊔s-ub₂
    ; ⊔-least = QC.⊔s-least
    ; _·_ = QC._·_
    ; e   = QC.e
    ; ·-mono = QC.·-mono
    ; ·-assoc    = ScaleLaxLaws.·-assoc L
    ; ·-idl      = ScaleLaxLaws.·-idl L
    ; ·-idr      = ScaleLaxLaws.·-idr L
    ; ·-distl-⊔  = ScaleLaxLaws.·-distl-⊔ L
    ; ·-distr-⊔  = ScaleLaxLaws.·-distr-⊔ L
    }
  where
    module QC = QAdapterCore C

    CPScale : ConPreorder ℓ
    CPScale =
      record
        { Con  = QC.Scale
        ; _⊑_  = QC._≤s_
        ; refl = QC.≤s-refl
        ; trans = QC.≤s-trans
        }

prequantaleFromCoreEq
  : ∀ {ℓ}
  → (C : QAdapterCore ℓ)
  → QAdapterEqLaws C
  → Prequantale {ℓ}
prequantaleFromCoreEq C E = prequantaleFromCoreLax C (scaleLaxLawsFromEq E)

prequantaleFromQAdapter : ∀ {ℓ} → QAdapter ℓ → Prequantale {ℓ}
prequantaleFromQAdapter Q = prequantaleFromCoreEq (qAdapterCore Q) (qAdapterEqLaws Q)

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
