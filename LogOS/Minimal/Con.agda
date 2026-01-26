{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Minimal.Con where

open import LogOS.Prelude.Level using (Level; lsuc; _⊔_; Lift; lift)
open import LogOS.Prelude.Relation.Binary.PropositionalEquality using (_≡_)
open import LogOS.Prelude.Product using (_,_)
open import LogOS.Syntax.Prop as Prop using (_≤Pred_; _∧_; _↔_; ↔-refl)

-- Minimal constraint carriers with preorder.
--
-- Note: despite the name, `ConPreorder` only provides reflexivity + transitivity
-- (a preorder). Antisymmetry is optional and captured separately by
-- `PartialOrder`.

record ConPreorder (ℓ : Level) : Set (lsuc ℓ) where
  infix 4 _⊑_
  field
    Con  : Set ℓ
    _⊑_  : Con → Con → Set ℓ
    refl : ∀ {c} → _⊑_ c c
    trans : ∀ {a b c} → _⊑_ a b → _⊑_ b c → _⊑_ a c

-- Degeneracy witness: the preorder relation is top (everything refines everything).
--
-- This is useful as an explicit “this model is vacuous at the order level”
-- marker for demo/scaffolding kernels, where flow/task inequalities should not
-- be interpreted semantically.

record TopOrder {ℓ : Level} (CP : ConPreorder ℓ) : Set (lsuc ℓ) where
  open ConPreorder CP
  field
    top : ∀ c d → _⊑_ c d

infix 4 _≈CP_
_≈CP_
  : ∀ {ℓ}
  → (CP : ConPreorder ℓ)
  → ConPreorder.Con CP → ConPreorder.Con CP → Set ℓ
_≈CP_ CP x y = ConPreorder._⊑_ CP x y ∧ ConPreorder._⊑_ CP y x

≈CP↔Le
  : ∀ {ℓ} {CP : ConPreorder ℓ} {x y : ConPreorder.Con CP}
  → Prop._↔_ (_≈CP_ CP x y)
              (ConPreorder._⊑_ CP x y ∧ ConPreorder._⊑_ CP y x)
≈CP↔Le {CP = CP} = Prop.↔-refl

≈CP-refl
  : ∀ {ℓ} (CP : ConPreorder ℓ) (c : ConPreorder.Con CP)
  → _≈CP_ CP c c
≈CP-refl CP c = (ConPreorder.refl CP , ConPreorder.refl CP)

≈CP-sym
  : ∀ {ℓ} {CP : ConPreorder ℓ} {c d : ConPreorder.Con CP}
  → _≈CP_ CP c d → _≈CP_ CP d c
≈CP-sym (cd , dc) = (dc , cd)

≈CP-trans
  : ∀ {ℓ} {CP : ConPreorder ℓ} {a b c : ConPreorder.Con CP}
  → _≈CP_ CP a b → _≈CP_ CP b c → _≈CP_ CP a c
≈CP-trans {CP = CP} (ab , ba) (bc , cb) =
  (ConPreorder.trans CP ab bc , ConPreorder.trans CP cb ba)

≡→≈CP
  : ∀ {ℓ} {CP : ConPreorder ℓ} {a b : ConPreorder.Con CP}
  → a ≡ b → _≈CP_ CP a b
≡→≈CP {CP = CP} eq rewrite eq = (ConPreorder.refl CP , ConPreorder.refl CP)

-- Monotonicity of an endomap on a constraint preorder.

MonoOn : ∀ {ℓ} (CP : ConPreorder ℓ) → (ConPreorder.Con CP → ConPreorder.Con CP) → Set ℓ
MonoOn CP f = ∀ {c d} → ConPreorder._⊑_ CP c d → ConPreorder._⊑_ CP (f c) (f d)

Respects≈
  : ∀ {ℓ} (CP : ConPreorder ℓ)
  → (ConPreorder.Con CP → ConPreorder.Con CP)
  → Set ℓ
Respects≈ CP f = ∀ {c d} → _≈CP_ CP c d → _≈CP_ CP (f c) (f d)

idMonoOn : ∀ {ℓ} {CP : ConPreorder ℓ} → MonoOn CP (λ x → x)
idMonoOn p = p

compMonoOn
  : ∀ {ℓ} {CP : ConPreorder ℓ}
    {f g : ConPreorder.Con CP → ConPreorder.Con CP}
  → MonoOn CP f
  → MonoOn CP g
  → MonoOn CP (λ x → g (f x))
compMonoOn monoF monoG p = monoG (monoF p)

monoOn-respects≈
  : ∀ {ℓ} {CP : ConPreorder ℓ}
    {f : ConPreorder.Con CP → ConPreorder.Con CP}
  → MonoOn CP f
  → Respects≈ CP f
monoOn-respects≈ {CP = CP} monoF (cd , dc) =
  (monoF cd , monoF dc)

-- Monotonicity of a map between two constraint preorders.

MonoMap
  : ∀ {ℓ₁ ℓ₂ : Level}
    (CP₁ : ConPreorder ℓ₁) (CP₂ : ConPreorder ℓ₂)
  → (ConPreorder.Con CP₁ → ConPreorder.Con CP₂)
  → Set (ℓ₁ ⊔ ℓ₂)
MonoMap CP₁ CP₂ f =
  ∀ {x y} → ConPreorder._⊑_ CP₁ x y → ConPreorder._⊑_ CP₂ (f x) (f y)

idMonoMap
  : ∀ {ℓ} {CP : ConPreorder ℓ}
  → MonoMap CP CP (λ x → x)
idMonoMap p = p

compMonoMap
  : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level}
    {CP₁ : ConPreorder ℓ₁} {CP₂ : ConPreorder ℓ₂} {CP₃ : ConPreorder ℓ₃}
    {f : ConPreorder.Con CP₁ → ConPreorder.Con CP₂}
    {g : ConPreorder.Con CP₂ → ConPreorder.Con CP₃}
  → MonoMap CP₁ CP₂ f
  → MonoMap CP₂ CP₃ g
  → MonoMap CP₁ CP₃ (λ x → g (f x))
compMonoMap monoF monoG p = monoG (monoF p)

monoMap-respects≈
  : ∀ {ℓ₁ ℓ₂ : Level}
    {CP₁ : ConPreorder ℓ₁} {CP₂ : ConPreorder ℓ₂}
    {f : ConPreorder.Con CP₁ → ConPreorder.Con CP₂}
  → MonoMap CP₁ CP₂ f
  → ∀ {x y} → _≈CP_ CP₁ x y → _≈CP_ CP₂ (f x) (f y)
monoMap-respects≈ monoF (xy , yx) = (monoF xy , monoF yx)

-- Predicates as constraints: for a carrier `A`, predicates `A → Set ℓ` form a
-- preorder under pointwise implication (`_≤Pred_`), lifted to avoid universe
-- mismatch (`ConPreorder` lives in one universe).

PredConPreorder : ∀ {ℓ} (A : Set ℓ) → ConPreorder (lsuc ℓ)
PredConPreorder {ℓ} A =
  record
    { Con  = A → Set ℓ
    ; _⊑_  = λ P Q → Lift (lsuc ℓ) (P ≤Pred Q)
    ; refl = lift (λ _ p → p)
    ; trans = λ pq qr → lift (λ a pa → Lift.lower qr a (Lift.lower pq a pa))
    }

-- Optionally distinguish bulk/boundary preorders

record BulkBoundary (ℓ : Level) : Set (lsuc ℓ) where
  field
    bulk : ConPreorder ℓ
    bnd  : ConPreorder ℓ

  open ConPreorder bulk public renaming (Con to Con_bulk; _⊑_ to _⊑bulk_)
  open ConPreorder bnd  public renaming (Con to Con_bnd;  _⊑_ to _⊑bnd_)

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

record PartialOrder {ℓ : Level} (CP : ConPreorder ℓ) : Set (lsuc ℓ) where
  open ConPreorder CP
  field
    antisym : ∀ {a b} → _⊑_ a b → _⊑_ b a → a ≡ b

record BulkBoundaryPO {ℓ : Level} (BB : BulkBoundary ℓ) : Set (lsuc ℓ) where
  open BulkBoundary BB
  field
    po-bulk : PartialOrder bulk
    po-bnd  : PartialOrder bnd

-- Antisymmetry upgrades mutual refinement to propositional equality.

≈CP→≡
  : ∀ {ℓ} {CP : ConPreorder ℓ}
  → PartialOrder CP
  → ∀ {a b : ConPreorder.Con CP}
  → _≈CP_ CP a b
  → a ≡ b
≈CP→≡ po (ab , ba) = PartialOrder.antisym po ab ba

≈bulk→≡
  : ∀ {ℓ} {BB : BulkBoundary ℓ}
  → BulkBoundaryPO BB
  → ∀ {a b : BulkBoundary.Con_bulk BB}
  → _≈bulk_ BB a b
  → a ≡ b
≈bulk→≡ po (ab , ba) =
  PartialOrder.antisym (BulkBoundaryPO.po-bulk po) ab ba

≈bnd→≡
  : ∀ {ℓ} {BB : BulkBoundary ℓ}
  → BulkBoundaryPO BB
  → ∀ {a b : BulkBoundary.Con_bnd BB}
  → _≈bnd_ BB a b
  → a ≡ b
≈bnd→≡ po (ab , ba) =
  PartialOrder.antisym (BulkBoundaryPO.po-bnd po) ab ba
