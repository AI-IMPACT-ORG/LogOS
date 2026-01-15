{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Minimal.Con where

open import Host.Level using (Level; lsuc; _⊔_; Lift; lift)
open import Data.Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (_,_)
open import LogOS.Syntax.Prop as Prop using (_≤Pred_; _∧_; _↔_; ↔-refl)

-- Minimal constraint carriers with preorder.
--
-- Note: despite the name, `ConPoset` only provides reflexivity + transitivity
-- (a preorder). Antisymmetry is optional and captured separately by
-- `PartialOrder`.

record ConPoset (ℓ : Level) : Set (lsuc ℓ) where
  infix 4 _⊑_
  field
    Con  : Set ℓ
    _⊑_  : Con → Con → Set ℓ
    refl : ∀ {c} → _⊑_ c c
    trans : ∀ {a b c} → _⊑_ a b → _⊑_ b c → _⊑_ a c

infix 4 _≈CP_
_≈CP_
  : ∀ {ℓ}
  → (CP : ConPoset ℓ)
  → ConPoset.Con CP → ConPoset.Con CP → Set ℓ
_≈CP_ CP x y = ConPoset._⊑_ CP x y ∧ ConPoset._⊑_ CP y x

≈CP↔Le
  : ∀ {ℓ} {CP : ConPoset ℓ} {x y : ConPoset.Con CP}
  → Prop._↔_ (_≈CP_ CP x y)
              (ConPoset._⊑_ CP x y ∧ ConPoset._⊑_ CP y x)
≈CP↔Le {CP = CP} = Prop.↔-refl

≈CP-refl
  : ∀ {ℓ} (CP : ConPoset ℓ) (c : ConPoset.Con CP)
  → _≈CP_ CP c c
≈CP-refl CP c = (ConPoset.refl CP , ConPoset.refl CP)

≈CP-sym
  : ∀ {ℓ} {CP : ConPoset ℓ} {c d : ConPoset.Con CP}
  → _≈CP_ CP c d → _≈CP_ CP d c
≈CP-sym (cd , dc) = (dc , cd)

≈CP-trans
  : ∀ {ℓ} {CP : ConPoset ℓ} {a b c : ConPoset.Con CP}
  → _≈CP_ CP a b → _≈CP_ CP b c → _≈CP_ CP a c
≈CP-trans {CP = CP} (ab , ba) (bc , cb) =
  (ConPoset.trans CP ab bc , ConPoset.trans CP cb ba)

-- Monotonicity of an endomap on a constraint poset.

MonoOn : ∀ {ℓ} (CP : ConPoset ℓ) → (ConPoset.Con CP → ConPoset.Con CP) → Set ℓ
MonoOn CP f = ∀ {c d} → ConPoset._⊑_ CP c d → ConPoset._⊑_ CP (f c) (f d)

Respects≈
  : ∀ {ℓ} (CP : ConPoset ℓ)
  → (ConPoset.Con CP → ConPoset.Con CP)
  → Set ℓ
Respects≈ CP f = ∀ {c d} → _≈CP_ CP c d → _≈CP_ CP (f c) (f d)

idMonoOn : ∀ {ℓ} {CP : ConPoset ℓ} → MonoOn CP (λ x → x)
idMonoOn p = p

compMonoOn
  : ∀ {ℓ} {CP : ConPoset ℓ}
    {f g : ConPoset.Con CP → ConPoset.Con CP}
  → MonoOn CP f
  → MonoOn CP g
  → MonoOn CP (λ x → g (f x))
compMonoOn monoF monoG p = monoG (monoF p)

monoOn-respects≈
  : ∀ {ℓ} {CP : ConPoset ℓ}
    {f : ConPoset.Con CP → ConPoset.Con CP}
  → MonoOn CP f
  → Respects≈ CP f
monoOn-respects≈ {CP = CP} monoF (cd , dc) =
  (monoF cd , monoF dc)

-- Monotonicity of a map between two constraint preorders.

MonoMap
  : ∀ {ℓ₁ ℓ₂ : Level}
    (CP₁ : ConPoset ℓ₁) (CP₂ : ConPoset ℓ₂)
  → (ConPoset.Con CP₁ → ConPoset.Con CP₂)
  → Set (ℓ₁ ⊔ ℓ₂)
MonoMap CP₁ CP₂ f =
  ∀ {x y} → ConPoset._⊑_ CP₁ x y → ConPoset._⊑_ CP₂ (f x) (f y)

idMonoMap
  : ∀ {ℓ} {CP : ConPoset ℓ}
  → MonoMap CP CP (λ x → x)
idMonoMap p = p

compMonoMap
  : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level}
    {CP₁ : ConPoset ℓ₁} {CP₂ : ConPoset ℓ₂} {CP₃ : ConPoset ℓ₃}
    {f : ConPoset.Con CP₁ → ConPoset.Con CP₂}
    {g : ConPoset.Con CP₂ → ConPoset.Con CP₃}
  → MonoMap CP₁ CP₂ f
  → MonoMap CP₂ CP₃ g
  → MonoMap CP₁ CP₃ (λ x → g (f x))
compMonoMap monoF monoG p = monoG (monoF p)

monoMap-respects≈
  : ∀ {ℓ₁ ℓ₂ : Level}
    {CP₁ : ConPoset ℓ₁} {CP₂ : ConPoset ℓ₂}
    {f : ConPoset.Con CP₁ → ConPoset.Con CP₂}
  → MonoMap CP₁ CP₂ f
  → ∀ {x y} → _≈CP_ CP₁ x y → _≈CP_ CP₂ (f x) (f y)
monoMap-respects≈ monoF (xy , yx) = (monoF xy , monoF yx)

-- Predicates as constraints: for a carrier `A`, predicates `A → Set ℓ` form a
-- preorder under pointwise implication (`_≤Pred_`), lifted to avoid universe
-- mismatch (`ConPoset` lives in one universe).

PredConPoset : ∀ {ℓ} (A : Set ℓ) → ConPoset (lsuc ℓ)
PredConPoset {ℓ} A =
  record
    { Con  = A → Set ℓ
    ; _⊑_  = λ P Q → Lift (lsuc ℓ) (P ≤Pred Q)
    ; refl = lift (λ _ p → p)
    ; trans = λ pq qr → lift (λ a pa → Lift.lower qr a (Lift.lower pq a pa))
    }

-- Optionally distinguish bulk/boundary posets

record BulkBoundary (ℓ : Level) : Set (lsuc ℓ) where
  field
    bulk : ConPoset ℓ
    bnd  : ConPoset ℓ

  open ConPoset bulk public renaming (Con to Con_bulk; _⊑_ to _⊑bulk_)
  open ConPoset bnd  public renaming (Con to Con_bnd;  _⊑_ to _⊑bnd_)

infix 4 _≈bulk_ _≈bnd_
_≈bulk_
  : ∀ {ℓ} (BB : BulkBoundary ℓ)
  → BulkBoundary.Con_bulk BB → BulkBoundary.Con_bulk BB → Set ℓ
_≈bulk_ BB = _≈CP_ (BulkBoundary.bulk BB)

_≈bnd_
  : ∀ {ℓ} (BB : BulkBoundary ℓ)
  → BulkBoundary.Con_bnd BB → BulkBoundary.Con_bnd BB → Set ℓ
_≈bnd_ BB = _≈CP_ (BulkBoundary.bnd BB)

-- Optional strengthening to partial orders (add antisymmetry)

record PartialOrder {ℓ : Level} (CP : ConPoset ℓ) : Set (lsuc ℓ) where
  open ConPoset CP
  field
    antisym : ∀ {a b} → _⊑_ a b → _⊑_ b a → a ≡ b

record BulkBoundaryPO {ℓ : Level} (BB : BulkBoundary ℓ) : Set (lsuc ℓ) where
  open BulkBoundary BB
  field
    po-bulk : PartialOrder bulk
    po-bnd  : PartialOrder bnd
