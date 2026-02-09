{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Minimal.RelPreorder where

-- A two-level preorder: the carrier and the relation may live in different
-- universes.
--
-- Motivation: observational relations induced by satisfaction predicates
-- (`ObsLeOn`) usually live in `ℓCtx ⊔ ℓSat`, not in the carrier level `ℓCon`.
-- This module provides a small target interface so such relations can be used
-- uniformly as view targets, without universe-lifting tricks.

open import LogOS.Prelude using (Level; _⊔_; lsuc; _≡_; _,_) renaming (refl to refl≡; trans to trans≡)
open import LogOS.Syntax.Prop as Prop using (_≤Pred_; _∧_; _↔_; ↔-refl)

record RelPreorder (ℓCon ℓRel : Level) : Set (lsuc (ℓCon ⊔ ℓRel)) where
  infix 4 _⊑_
  field
    Con  : Set ℓCon
    _⊑_  : Con → Con → Set ℓRel
    refl : ∀ {c} → _⊑_ c c
    trans : ∀ {a b c} → _⊑_ a b → _⊑_ b c → _⊑_ a c

infix 4 _≈RP_
_≈RP_
  : ∀ {ℓCon ℓRel}
  → (RP : RelPreorder ℓCon ℓRel)
  → RelPreorder.Con RP → RelPreorder.Con RP → Set ℓRel
_≈RP_ RP x y = RelPreorder._⊑_ RP x y ∧ RelPreorder._⊑_ RP y x

≈RP↔Le
  : ∀ {ℓCon ℓRel} {RP : RelPreorder ℓCon ℓRel} {x y : RelPreorder.Con RP}
  → Prop._↔_ (_≈RP_ RP x y)
              (RelPreorder._⊑_ RP x y ∧ RelPreorder._⊑_ RP y x)
≈RP↔Le {RP = _} = ↔-refl

-- Directional projections (canonical names).
≈RP⇒
  : ∀ {ℓCon ℓRel} {RP : RelPreorder ℓCon ℓRel} {x y : RelPreorder.Con RP}
  → _≈RP_ RP x y
  → RelPreorder._⊑_ RP x y
≈RP⇒ (xy , _) = xy

≈RP⇐
  : ∀ {ℓCon ℓRel} {RP : RelPreorder ℓCon ℓRel} {x y : RelPreorder.Con RP}
  → _≈RP_ RP x y
  → RelPreorder._⊑_ RP y x
≈RP⇐ (_ , yx) = yx

≈RP-refl
  : ∀ {ℓCon ℓRel} (RP : RelPreorder ℓCon ℓRel) (c : RelPreorder.Con RP)
  → _≈RP_ RP c c
≈RP-refl RP c = (RelPreorder.refl RP , RelPreorder.refl RP)

≈RP-sym
  : ∀ {ℓCon ℓRel} {RP : RelPreorder ℓCon ℓRel} {c d : RelPreorder.Con RP}
  → _≈RP_ RP c d → _≈RP_ RP d c
≈RP-sym (cd , dc) = (dc , cd)

≈RP-trans
  : ∀ {ℓCon ℓRel} {RP : RelPreorder ℓCon ℓRel} {a b c : RelPreorder.Con RP}
  → _≈RP_ RP a b → _≈RP_ RP b c → _≈RP_ RP a c
≈RP-trans {RP = RP} (ab , ba) (bc , cb) =
  (RelPreorder.trans RP ab bc , RelPreorder.trans RP cb ba)

≡→≈RP
  : ∀ {ℓCon ℓRel} {RP : RelPreorder ℓCon ℓRel} {a b : RelPreorder.Con RP}
  → a ≡ b → _≈RP_ RP a b
≡→≈RP {RP = RP} eq rewrite eq = (RelPreorder.refl RP , RelPreorder.refl RP)

-- Equality as a preorder target (useful as the semantic target for strict views).
EqRelPreorder : ∀ {ℓ} (X : Set ℓ) → RelPreorder ℓ ℓ
EqRelPreorder X =
  record
    { Con = X
    ; _⊑_ = _≡_
    ; refl = refl≡
    ; trans = trans≡
    }

-- Predicates as a two-level preorder target:
-- carrier at `lsuc ℓ`, relation at `ℓ`.
PredRelPreorder : ∀ {ℓ} (A : Set ℓ) → RelPreorder (lsuc ℓ) ℓ
PredRelPreorder {ℓ} A =
  record
    { Con = A → Set ℓ
    ; _⊑_ = _≤Pred_
    ; refl = λ _ p → p
    ; trans = λ pq qr a pa → qr a (pq a pa)
    }
